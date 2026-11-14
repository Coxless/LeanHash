//! P0' 試作2（手書き）：ブロック 1KB、短い入力の専用経路、1 ブロック以内は multiply-shift で仕上げ。
//!
//! 入力長 L で経路が分かれる（どれも同じ NH の特殊化として書ける）:
//! - **L ≤ 1024（1 ブロック）:** 語の組 (a_i, b_i) と長さの組 (L, 0) に NH64 をかけて 128bit acc を得る。
//!   acc を multiply-shift `hi64(m · acc mod 2^128)`（m は奇数の鍵）で 64bit に落とし、fin と XOR して fmix64。
//!   語の取り出しは長さごとに単射（L ≤ 16 は xxh3 風の重なり読み、それ以上は最後の組を末尾 16 バイトから重ねて読む）。
//!   ε ≤ ε_NH + 2^-63。ε_NH は組数によらず 2^-64（長さの組が最後の位置にあるため。Lean の `pathA_eps` / `pathB_eps`）。
//!   経路ごとに独立な fin（`fin` / `fin_mid` / `fin_long`）を使うので、経路をまたぐ 2 入力の衝突確率は 2^-64
//! - **L > 1024:** 1KB ごとの NH64（長さの組なし）→ 60bit limb で多項式 mod 2^61−1 → 長さ係数 →
//!   `(h<<3 | t>>61) ^ fin` を fmix64。ε ≤ 2^-64 + (3n+1)/p

// 計算の核（NH のレーン・組、Horner、multiply-shift、limb、仕上げ）は HashIR から生成したもの（`kernel.rs`、
// 仕様との一致は Lean の `LeanHash/Impl/Equiv.lean`）。バイトの読み出し・ループ・SIMD・経路の分岐は手書き。
// その外側（スカラー版）と同じ形で核を組んだ Lean の参照実装 `hashCI`（`LeanHash/Impl/Outer.lean`）は
// 仕様と一致することを証明済み（`LeanHash/Impl/OuterEquiv.lean` の `hashCI_eq`）。この Rust と参照実装の一致は
// 差分テスト（下の `lean_ref`）で見る。外側の Rust そのものの検証は P3.5（Aeneas）。
use crate::kernel::{finish, horner, limb0, limb1, limb2, ms, nh32_lane, nh_pair};
use crate::{splitmix64, P};

pub const BLOCK_BYTES: usize = 1024;
const PAIRS: usize = BLOCK_BYTES / 16; // 64
const KEY_WORDS: usize = 2 * PAIRS + 2; // データ用 128 語 + 長さの組 2 語

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Keys {
    pub nh: [u64; KEY_WORDS],
    /// multiply-shift の乗数（奇数）
    pub m: u128,
    pub r: u64,
    /// 仕上げの XOR 定数。経路ごとに独立（経路をまたぐ 2 入力の衝突確率を 2^-64 にするため。
    /// Lean の `card_out_collide`、docs/journal/2026-11-10-per-path-fin.md）。
    /// `fin` は 1KB 以下の NH64 経路（`hash`。v2c では 32 バイト以下）、`fin_mid` は v2c の 33..=1024 の NH32x2 経路、
    /// `fin_long` は 1KB より長い経路（`hash_long` / `hash_long_b`）
    pub fin: u64,
    pub fin_mid: u64,
    pub fin_long: u64,
}

impl Keys {
    pub fn from_seed(seed: u64) -> Self {
        let mut s = seed;
        let mut nh = [0u64; KEY_WORDS];
        for k in nh.iter_mut() {
            *k = splitmix64(&mut s);
        }
        let m = (((splitmix64(&mut s) as u128) << 64) | splitmix64(&mut s) as u128) | 1;
        let r = loop {
            let v = splitmix64(&mut s) >> 3;
            if v < P {
                break v;
            }
        };
        let fin = splitmix64(&mut s);
        // 既存の鍵の値を変えないよう、追加の鍵は最後に引く
        let fin_mid = splitmix64(&mut s);
        let fin_long = splitmix64(&mut s);
        Keys { nh, m, r, fin, fin_mid, fin_long }
    }
}

#[inline(always)]
fn rd64(b: &[u8], i: usize) -> u64 {
    u64::from_le_bytes(b[i..i + 8].try_into().unwrap())
}

#[inline(always)]
fn rd32(b: &[u8], i: usize) -> u64 {
    u32::from_le_bytes(b[i..i + 4].try_into().unwrap()) as u64
}

/// 1 ブロック全体の NH64（4 本の独立な和にして命令レベル並列を稼ぐ）。
#[inline(always)]
fn nh_full_block(k: &[u64; KEY_WORDS], b: &[u8]) -> u128 {
    let mut acc = [0u128; 4];
    for (bc, kc) in b.chunks_exact(64).zip(k.chunks_exact(8)) {
        for j in 0..4 {
            acc[j] = acc[j].wrapping_add(nh_pair(rd64(bc, 16 * j), rd64(bc, 16 * j + 8), kc[2 * j], kc[2 * j + 1]));
        }
    }
    acc[0].wrapping_add(acc[1]).wrapping_add(acc[2].wrapping_add(acc[3]))
}

/// 長さ len（1..=1024）の部分の NH64。最後の組は末尾 16 バイトから重ねて読む（len ≥ 16 のとき）。
#[inline(always)]
fn nh_partial(k: &[u64; KEY_WORDS], b: &[u8]) -> u128 {
    let len = b.len();
    if len <= 16 {
        let (x, y) = if len >= 8 {
            (rd64(b, 0), rd64(b, len - 8))
        } else if len >= 4 {
            (rd32(b, 0), rd32(b, len - 4))
        } else if len > 0 {
            (b[0] as u64 | (b[len / 2] as u64) << 8 | (b[len - 1] as u64) << 16, 0)
        } else {
            return 0;
        };
        return nh_pair(x, y, k[0], k[1]);
    }
    let pairs = len.div_ceil(16);
    // 最後の組以外は前から 16 バイトずつ、最後の組は末尾 16 バイト
    let body = &b[..16 * (pairs - 1)];
    let mut acc0 = 0u128;
    let mut acc1 = 0u128;
    let mut it = body.chunks_exact(32).zip(k.chunks_exact(4));
    for (bc, kc) in &mut it {
        acc0 = acc0.wrapping_add(nh_pair(rd64(bc, 0), rd64(bc, 8), kc[0], kc[1]));
        acc1 = acc1.wrapping_add(nh_pair(rd64(bc, 16), rd64(bc, 24), kc[2], kc[3]));
    }
    if !body.len().is_multiple_of(32) {
        let p = pairs - 2;
        acc0 = acc0.wrapping_add(nh_pair(rd64(b, 16 * p), rd64(b, 16 * p + 8), k[2 * p], k[2 * p + 1]));
    }
    let q = pairs - 1;
    acc1 = acc1.wrapping_add(nh_pair(rd64(b, len - 16), rd64(b, len - 8), k[2 * q], k[2 * q + 1]));
    acc0.wrapping_add(acc1)
}

#[inline]
pub fn hash(k: &Keys, data: &[u8]) -> u64 {
    let len = data.len();
    if len <= BLOCK_BYTES {
        let acc = nh_partial(&k.nh, data).wrapping_add(nh_pair(len as u64, 0, k.nh[2 * PAIRS], k.nh[2 * PAIRS + 1]));
        return finish(ms(k.m, acc), k.fin);
    }
    hash_long(k, data)
}

#[inline(never)]
fn hash_long(k: &Keys, data: &[u8]) -> u64 {
    let mut h = 0u64;
    let mut t = 0u64;
    let mut absorb = |acc: u128| {
        let lo = acc as u64;
        let hi = (acc >> 64) as u64;
        h = horner(h, k.r, limb0(lo));
        h = horner(h, k.r, limb1(lo, hi));
        h = horner(h, k.r, limb2(hi));
        t = t.wrapping_add(hi);
    };
    let mut blocks = data.chunks_exact(BLOCK_BYTES);
    for b in &mut blocks {
        absorb(nh_full_block(&k.nh, b));
    }
    let rem = blocks.remainder().len();
    if rem > 0 {
        // 端数は直前のブロックと重ねて末尾 rem バイトぶんの組を読む（len > 1024 なので常に 16 バイト以上ある）
        let tail = &data[data.len() - rem.max(16)..];
        absorb(nh_partial(&k.nh, tail));
    }
    let h = horner(h, k.r, data.len() as u64);
    finish((h << 3) | (t >> 61), k.fin_long)
}

// ---------------------------------------------------------------------------
// 試作2b: 長い入力を NH32 の Toeplitz 2 本（鍵を 1 レーンずらす）で処理する。
// 1 レーン = 64bit = (偶数語, 奇数語) の u32 組。積は 32×32→64 なので AVX2/AVX-512 の vpmuludq に乗る。
// 1 本の NH32 は ε = 2^-32、鍵をずらした 2 本で ε = 2^-64（UMAC の Toeplitz 構成）。

#[inline(always)]
fn nh32x2_full_block(k: &[u64; KEY_WORDS], b: &[u8]) -> (u64, u64) {
    let b: &[u8; BLOCK_BYTES] = b.try_into().unwrap();
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    {
        // SAFETY: avx2 はコンパイル時に有効。読み込みはすべて b（1024B）と k（130 語）の範囲内。
        unsafe { nh32x2_block_avx2(k, b) }
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
    {
        nh32x2_block_scalar(k, b)
    }
}

#[allow(dead_code)]
#[inline(always)]
fn nh32x2_block_scalar(k: &[u64; KEY_WORDS], b: &[u8; BLOCK_BYTES]) -> (u64, u64) {
    let mut a1 = [0u64; 8];
    let mut a2 = [0u64; 8];
    for c in 0..BLOCK_BYTES / 64 {
        for j in 0..8 {
            let i = 8 * c + j;
            let v = u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap());
            a1[j] = a1[j].wrapping_add(nh32_lane(v, k[i]));
            a2[j] = a2[j].wrapping_add(nh32_lane(v, k[i + 1]));
        }
    }
    (a1.iter().fold(0u64, |s, x| s.wrapping_add(*x)), a2.iter().fold(0u64, |s, x| s.wrapping_add(*x)))
}

/// AVX2 版。1 命令で 4 レーン: `_mm256_add_epi32` が各 u32 の mod 2^32 加算、
/// `_mm256_mul_epu32(s, s >> 32)` が各レーンの lo(s)·hi(s)（32×32→64）。
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[inline(always)]
unsafe fn nh32x2_block_avx2(k: &[u64; KEY_WORDS], b: &[u8; BLOCK_BYTES]) -> (u64, u64) {
    use core::arch::x86_64::*;
    let mut a1 = [_mm256_setzero_si256(); 2];
    let mut a2 = [_mm256_setzero_si256(); 2];
    let bp = b.as_ptr() as *const __m256i;
    let kp = k.as_ptr();
    for i in 0..BLOCK_BYTES / 32 {
        let v = _mm256_loadu_si256(bp.add(i));
        let k1 = _mm256_loadu_si256(kp.add(4 * i) as *const __m256i);
        let k2 = _mm256_loadu_si256(kp.add(4 * i + 1) as *const __m256i);
        let s1 = _mm256_add_epi32(v, k1);
        let s2 = _mm256_add_epi32(v, k2);
        let p1 = _mm256_mul_epu32(s1, _mm256_srli_epi64::<32>(s1));
        let p2 = _mm256_mul_epu32(s2, _mm256_srli_epi64::<32>(s2));
        a1[i % 2] = _mm256_add_epi64(a1[i % 2], p1);
        a2[i % 2] = _mm256_add_epi64(a2[i % 2], p2);
    }
    let mut o1 = [0u64; 4];
    let mut o2 = [0u64; 4];
    _mm256_storeu_si256(o1.as_mut_ptr() as *mut __m256i, _mm256_add_epi64(a1[0], a1[1]));
    _mm256_storeu_si256(o2.as_mut_ptr() as *mut __m256i, _mm256_add_epi64(a2[0], a2[1]));
    (o1.iter().fold(0u64, |s, x| s.wrapping_add(*x)), o2.iter().fold(0u64, |s, x| s.wrapping_add(*x)))
}

#[allow(unused_assignments)]
/// 長さ 8..=1024 の端数の NH32x2。32 バイト単位は SIMD、残りのレーンはスカラー、最後のレーンは末尾 8 バイトから重ねて読む。
#[inline(always)]
fn nh32x2_partial(k: &[u64; KEY_WORDS], b: &[u8]) -> (u64, u64) {
    let len = b.len();
    let lanes = len.div_ceil(8);
    #[allow(unused_mut)]
    let (mut s1, mut s2, mut i) = (0u64, 0u64, 0usize);
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    unsafe {
        // SAFETY: 読むのは b[0..32*chunks] と k[0..4*chunks+5]（chunks*4 ≤ lanes-1 ≤ 127）
        use core::arch::x86_64::*;
        let chunks = (lanes - 1) / 4;
        let mut a1 = _mm256_setzero_si256();
        let mut a2 = _mm256_setzero_si256();
        for c in 0..chunks {
            let v = _mm256_loadu_si256(b.as_ptr().add(32 * c) as *const __m256i);
            let k1 = _mm256_loadu_si256(k.as_ptr().add(4 * c) as *const __m256i);
            let k2 = _mm256_loadu_si256(k.as_ptr().add(4 * c + 1) as *const __m256i);
            let x1 = _mm256_add_epi32(v, k1);
            let x2 = _mm256_add_epi32(v, k2);
            a1 = _mm256_add_epi64(a1, _mm256_mul_epu32(x1, _mm256_srli_epi64::<32>(x1)));
            a2 = _mm256_add_epi64(a2, _mm256_mul_epu32(x2, _mm256_srli_epi64::<32>(x2)));
        }
        let mut o = [0u64; 8];
        _mm256_storeu_si256(o.as_mut_ptr() as *mut __m256i, a1);
        _mm256_storeu_si256(o.as_mut_ptr().add(4) as *mut __m256i, a2);
        s1 = o[0].wrapping_add(o[1]).wrapping_add(o[2].wrapping_add(o[3]));
        s2 = o[4].wrapping_add(o[5]).wrapping_add(o[6].wrapping_add(o[7]));
        i = 4 * chunks;
    }
    while i < lanes {
        let v = if i + 1 == lanes { rd64(b, len - 8) } else { rd64(b, 8 * i) };
        s1 = s1.wrapping_add(nh32_lane(v, k[i]));
        s2 = s2.wrapping_add(nh32_lane(v, k[i + 1]));
        i += 1;
    }
    (s1, s2)
}

/// 試作2c。32 バイト以下は NH64（`hash` と同じ）、33..=1024 は NH32x2 + 長さレーン → multiply-shift、
/// それより長い入力は 2b と同じ。
#[inline]
pub fn hash_c(k: &Keys, data: &[u8]) -> u64 {
    let len = data.len();
    if len <= 32 {
        return hash(k, data);
    }
    if len <= BLOCK_BYTES {
        let (x, y) = nh32x2_partial(&k.nh, data);
        // 長さレーン（鍵は最後の 2 語）を足す
        let x = x.wrapping_add(nh32_lane(len as u64, k.nh[KEY_WORDS - 2]));
        let y = y.wrapping_add(nh32_lane(len as u64, k.nh[KEY_WORDS - 1]));
        return finish(ms(k.m, ((y as u128) << 64) | x as u128), k.fin_mid);
    }
    hash_long_b(k, data)
}

/// 試作2b。1 ブロック以内は `hash` と同じ（NH64 + multiply-shift）、それより長い入力だけ NH32x2。
#[inline]
pub fn hash_b(k: &Keys, data: &[u8]) -> u64 {
    if data.len() <= BLOCK_BYTES {
        return hash(k, data);
    }
    hash_long_b(k, data)
}

#[inline(never)]
fn hash_long_b(k: &Keys, data: &[u8]) -> u64 {
    let mut h = 0u64;
    let mut t = 0u64;
    let mut absorb = |(x, y): (u64, u64)| {
        h = horner(h, k.r, limb0(x));
        h = horner(h, k.r, limb1(x, y));
        h = horner(h, k.r, limb2(y));
        t = t.wrapping_add(y);
    };
    let mut blocks = data.chunks_exact(BLOCK_BYTES);
    for b in &mut blocks {
        absorb(nh32x2_full_block(&k.nh, b));
    }
    // 最後の NH には長さレーン（鍵の位置 128、Toeplitz の並びのまま）を必ず足す。
    // 長さを多項式の定数項だけで入れると、0 埋め入力の L と L+1 で出力前の値が +1 しか違わず、
    // SMHasher3 の SeedZeroes（差分分布）で偏りが出た（journal 参照）。
    let len = data.len() as u64;
    let rem = blocks.remainder().len();
    let (mut x, mut y) = if rem > 0 { nh32x2_partial(&k.nh, &data[data.len() - rem.max(8)..]) } else { (0, 0) };
    x = x.wrapping_add(nh32_lane(len, k.nh[KEY_WORDS - 2]));
    y = y.wrapping_add(nh32_lane(len, k.nh[KEY_WORDS - 1]));
    absorb((x, y));
    let h = horner(h, k.r, len);
    // 仕上げは 1 ブロック以内と同じ multiply-shift → fmix64（(h, t) ↦ 128bit は単射）
    // horner の c に長さを渡す。生成した核の証明（`hornerK_eq`）は c < 2^63 を仮定する（len < 2^63 で成り立つ）
    finish(ms(k.m, ((h as u128) << 64) | t as u128), k.fin_long)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn distinct_on_small_structured_inputs() {
        // 0 埋めと紛らわしい入力、重なり読みの境界（3/4/8/9/16/17/1024/1025 バイト付近）で衝突しないこと
        let k = Keys::from_seed(5);
        let mut seen = HashSet::new();
        for n in 0..2100 {
            assert!(seen.insert(hash(&k, &vec![0u8; n])), "zeros len {n}");
        }
        for n in 0..40usize {
            for pos in 0..n {
                for v in [1u8, 0x80, 0xff] {
                    let mut x = vec![0u8; n];
                    x[pos] = v;
                    assert!(seen.insert(hash(&k, &x)), "len {n} pos {pos} v {v}");
                }
            }
        }
    }

    #[test]
    fn nh32_lane_matches_definition() {
        let mut s = 9u64;
        for _ in 0..100_000 {
            let v = splitmix64(&mut s);
            let k = splitmix64(&mut s);
            let lo = (v as u32).wrapping_add(k as u32) as u64;
            let hi = ((v >> 32) as u32).wrapping_add((k >> 32) as u32) as u64;
            assert_eq!(nh32_lane(v, k), lo * hi);
        }
    }

    #[test]
    fn simd_block_matches_scalar() {
        let k = Keys::from_seed(21);
        let mut s = 1u64;
        for _ in 0..200 {
            let b: Vec<u8> = (0..BLOCK_BYTES).map(|_| splitmix64(&mut s) as u8).collect();
            let b: &[u8; BLOCK_BYTES] = b.as_slice().try_into().unwrap();
            assert_eq!(nh32x2_full_block(&k.nh, b), nh32x2_block_scalar(&k.nh, b));
        }
    }

    #[test]
    fn partial_simd_matches_scalar() {
        let k = Keys::from_seed(22);
        let mut s = 2u64;
        for len in 8..=BLOCK_BYTES {
            let b: Vec<u8> = (0..len).map(|_| splitmix64(&mut s) as u8).collect();
            let lanes = len.div_ceil(8);
            let (mut s1, mut s2) = (0u64, 0u64);
            for i in 0..lanes {
                let v = if i + 1 == lanes { rd64(&b, len - 8) } else { rd64(&b, 8 * i) };
                s1 = s1.wrapping_add(nh32_lane(v, k.nh[i]));
                s2 = s2.wrapping_add(nh32_lane(v, k.nh[i + 1]));
            }
            assert_eq!(nh32x2_partial(&k.nh, &b), (s1, s2), "len {len}");
        }
    }

    #[test]
    fn every_byte_matters_c() {
        let k = Keys::from_seed(13);
        for n in [33usize, 40, 63, 64, 65, 100, 128, 129, 1000, 1024, 1025, 3000] {
            let base: Vec<u8> = (0..n).map(|i| (i * 7 + 3) as u8).collect();
            let h0 = hash_c(&k, &base);
            for pos in 0..n {
                let mut x = base.clone();
                x[pos] ^= 1;
                assert_ne!(hash_c(&k, &x), h0, "len {n} pos {pos}");
            }
        }
        let mut seen = std::collections::HashSet::new();
        for n in 0..2100 {
            assert!(seen.insert(hash_c(&k, &vec![0u8; n])), "zeros len {n}");
        }
    }

    #[test]
    fn every_byte_matters_b() {
        let k = Keys::from_seed(12);
        for n in [1025usize, 1031, 1032, 1033, 2048, 2049, 5000] {
            let base: Vec<u8> = (0..n).map(|i| (i * 7 + 3) as u8).collect();
            let h0 = hash_b(&k, &base);
            for pos in 0..n {
                let mut x = base.clone();
                x[pos] ^= 1;
                assert_ne!(hash_b(&k, &x), h0, "len {n} pos {pos}");
            }
        }
    }

    #[test]
    fn every_byte_matters_across_paths() {
        let k = Keys::from_seed(11);
        for n in [1usize, 2, 3, 4, 7, 8, 9, 15, 16, 17, 31, 32, 33, 1023, 1024, 1025, 1040, 3000] {
            let base: Vec<u8> = (0..n).map(|i| (i * 7 + 3) as u8).collect();
            let h0 = hash(&k, &base);
            for pos in 0..n {
                let mut x = base.clone();
                x[pos] ^= 1;
                assert_ne!(hash(&k, &x), h0, "len {n} pos {pos}");
            }
        }
    }

    /// Lean の仕様（`LeanHash/Spec/Encode.lean` の msgA / msgB、`Props/Toeplitz.lean` の nhO / nhT、
    /// `Props/ShortPath.lean` の accA / accB → ms → fmix64）を素朴に写したもの。`hash_c` と全長で一致すること。
    mod lean_spec {
        use super::super::*;
        use crate::fmix64;

        /// multiply-shift（仕様 `Props.ms 128 64` の素朴な写し）。
        fn ms(m: u128, x: u128) -> u64 {
            (m.wrapping_mul(x) >> 64) as u64
        }

        fn byte_at(s: &[u8], i: usize) -> u128 {
            s.get(i).copied().unwrap_or(0) as u128
        }

        fn read_le(k: usize, s: &[u8], o: usize) -> u128 {
            (0..k).map(|j| byte_at(s, o + j) << (8 * j)).sum()
        }

        fn short_pair(s: &[u8]) -> (u128, u128) {
            let l = s.len();
            if 8 <= l {
                (read_le(8, s, 0), read_le(8, s, l - 8))
            } else if 4 <= l {
                (read_le(4, s, 0), read_le(4, s, l - 4))
            } else {
                (byte_at(s, 0) + 256 * byte_at(s, l / 2) + 65536 * byte_at(s, l - 1), 0)
            }
        }

        fn msg_a(s: &[u8]) -> Vec<Option<(u128, u128)>> {
            let l = s.len();
            (0..65)
                .map(|i| {
                    if i == 64 {
                        Some((l as u128, 0))
                    } else if i == 0 {
                        if l == 0 {
                            None
                        } else if l <= 16 {
                            Some(short_pair(s))
                        } else {
                            Some((read_le(8, s, 0), read_le(8, s, 8)))
                        }
                    } else if i == 1 && 16 < l {
                        Some((read_le(8, s, l - 16), read_le(8, s, l - 8)))
                    } else {
                        None
                    }
                })
                .collect()
        }

        fn msg_b(s: &[u8]) -> Vec<Option<(u128, u128)>> {
            let l = s.len();
            let lanes = l.div_ceil(8);
            (0..129)
                .map(|i| {
                    if i == 128 {
                        Some((l as u128, 0))
                    } else if i + 1 < lanes {
                        Some((read_le(4, s, 8 * i), read_le(4, s, 8 * i + 4)))
                    } else if i + 1 == lanes {
                        Some((read_le(4, s, l - 8), read_le(4, s, l - 4)))
                    } else {
                        None
                    }
                })
                .collect()
        }

        /// 有無つき NH：Σ ((m1+k1) mod W)·((m2+k2) mod W) mod W²（W = 2^bits）
        fn nh_o(keys: &[(u128, u128)], msg: &[Option<(u128, u128)>], bits: u32) -> u128 {
            let w = 1u128.checked_shl(bits);
            let modw = |x: u128| match w {
                Some(w) => x % w,
                None => x,
            };
            let mut acc = 0u128;
            for (m, k) in msg.iter().zip(keys) {
                if let Some((m1, m2)) = m {
                    let a = modw(m1.wrapping_add(k.0) & u64::MAX as u128);
                    let b = modw(m2.wrapping_add(k.1) & u64::MAX as u128);
                    let p = a.wrapping_mul(b);
                    acc = if bits == 32 { (acc + p) & u64::MAX as u128 } else { acc.wrapping_add(p) };
                }
            }
            acc
        }

        pub fn hash_spec(k: &Keys, s: &[u8]) -> u64 {
            let (acc, fin) = if s.len() <= 32 {
                let keys: Vec<(u128, u128)> = (0..65).map(|i| (k.nh[2 * i] as u128, k.nh[2 * i + 1] as u128)).collect();
                (nh_o(&keys, &msg_a(s), 64), k.fin)
            } else {
                let lanes: Vec<(u128, u128)> =
                    (0..130).map(|i| ((k.nh[i] & 0xffff_ffff) as u128, (k.nh[i] >> 32) as u128)).collect();
                let m = msg_b(s);
                let x = nh_o(&lanes[..129], &m, 32);
                let y = nh_o(&lanes[1..], &m, 32);
                ((y << 64) | x, k.fin_mid)
            };
            fmix64(ms(k.m, acc) ^ fin)
        }

        /// 長い経路（L > 1024）。`LeanHash/Spec/Long.lean` の msgL と `Props/Long.lean` の
        /// outL → limbs → polyH（Horner mod p、最後に L）/ tsum → ms → fmix64 を素朴に写したもの。
        pub fn hash_long_spec(k: &Keys, s: &[u8]) -> u64 {
            let l = s.len();
            let p = crate::P as u128;
            let lanes: Vec<(u128, u128)> =
                (0..130).map(|i| ((k.nh[i] & 0xffff_ffff) as u128, (k.nh[i] >> 32) as u128)).collect();
            let nb = l / 1024;
            let (mut h, mut t) = (0u128, 0u128);
            for j in 0..nb + 1 {
                let msg: Vec<Option<(u128, u128)>> = if j < nb {
                    // msgFull：完全ブロックを msgB で読み、レーン 128 はなし
                    let mut m = msg_b(&s[1024 * j..1024 * j + 1024]);
                    m[128] = None;
                    m
                } else {
                    // msgLast：末尾 max(rem, 8) バイトを msgB で読み（rem = 0 ならなし）、レーン 128 は長さ
                    let rem = l % 1024;
                    let mut m = if rem == 0 { vec![None; 129] } else { msg_b(&s[l - rem.max(8)..]) };
                    m[128] = Some(((l as u128) & 0xffff_ffff, ((l as u128) >> 32) & 0xffff_ffff));
                    m
                };
                let x = nh_o(&lanes[..129], &msg, 32);
                let y = nh_o(&lanes[1..], &msg, 32);
                let v = x | (y << 64);
                let mask = (1u128 << 60) - 1;
                for c in [v & mask, (v >> 60) & mask, v >> 120] {
                    h = (h * k.r as u128 + c) % p;
                }
                t = (t + y) % (1u128 << 64);
            }
            h = (h * k.r as u128 + l as u128) % p;
            fmix64(ms(k.m, (h << 64) | t) ^ k.fin_long)
        }
    }

    #[test]
    fn lean_spec_matches_hash_long() {
        let mut s = 78u64;
        for seed in [1u64, 2, 3] {
            let k = Keys::from_seed(seed);
            let lens =
                (1025..=1100).chain([2047, 2048, 2049, 2050, 2055, 2056, 2057, 3071, 3072, 3073, 4096, 5000, 9000]);
            for len in lens {
                for _ in 0..2 {
                    let b: Vec<u8> = (0..len).map(|_| splitmix64(&mut s) as u8).collect();
                    assert_eq!(lean_spec::hash_long_spec(&k, &b), hash_c(&k, &b), "seed {seed} len {len}");
                }
            }
        }
    }

    #[test]
    fn lean_spec_matches_hash_c() {
        let mut s = 77u64;
        for seed in [1u64, 2, 3] {
            let k = Keys::from_seed(seed);
            for len in 0..=BLOCK_BYTES {
                for _ in 0..3 {
                    let b: Vec<u8> = (0..len).map(|_| splitmix64(&mut s) as u8).collect();
                    assert_eq!(lean_spec::hash_spec(&k, &b), hash_c(&k, &b), "seed {seed} len {len}");
                }
            }
        }
    }
}

/// 生成した核に切り替える前（手書きの核、commit 64a56fa）の出力との差分テスト。
/// 値は切り替え前に同じ入力で計算したもの（scalar と `-C target-cpu=native` で同じ値）。
#[cfg(test)]
mod golden {
    use super::*;

    #[test]
    fn matches_handwritten_kernels() {
        let mut acc = 0u64;
        let mut s = 99u64;
        for seed in [1u64, 2, 3, 0xdead_beef] {
            let k = Keys::from_seed(seed);
            for len in (0..=4200).chain([8191, 8192, 8193, 65536, 100_000]) {
                let b: Vec<u8> = (0..len).map(|_| splitmix64(&mut s) as u8).collect();
                acc = acc.rotate_left(5) ^ hash_c(&k, &b);
                acc = acc.rotate_left(5) ^ hash(&k, &b);
                acc = acc.rotate_left(5) ^ hash_b(&k, &b);
            }
        }
        assert_eq!(acc, 0x8c5d62ac59bb4b5b);
    }
}

/// Lean の参照実装 `hashCI`（`LeanHash/Impl/Outer.lean`。仕様 `Props.hashV2c` との一致は
/// `LeanHash/Impl/OuterEquiv.lean` の `hashCI_eq`）が出したテストベクトルとの差分テスト。
/// ベクトルは `lake exe ref_vectors rust/leanhash/src/lean_ref_vectors.txt` で作る（`LeanHash/Impl/RefMain.lean`）。
/// 鍵は `Keys::from_seed`、入力は状態 0x1234 から続けた splitmix64 の下位 8bit（seed・長さの順）。
#[cfg(test)]
mod lean_ref {
    use super::*;

    const VECTORS: &str = include_str!("lean_ref_vectors.txt");
    const SEEDS: [u64; 4] = [1, 2, 3, 0xdead_beef];

    fn lengths() -> Vec<usize> {
        let mut v: Vec<usize> = (0..=40).collect();
        v.extend([
            63, 64, 65, 100, 127, 128, 129, 1000, 1016, 1017, 1023, 1024, 1025, 1026, 1031, 1032, 1033, 1040, 2047,
            2048, 2049, 2055, 2056, 2057, 3000, 3072, 3073, 4096, 5000,
        ]);
        v
    }

    #[test]
    fn matches_lean_reference() {
        let mut lines = VECTORS.lines();
        let mut st = 0x1234u64;
        let mut n = 0;
        for seed in SEEDS {
            let k = Keys::from_seed(seed);
            for len in lengths() {
                let b: Vec<u8> = (0..len).map(|_| splitmix64(&mut st) as u8).collect();
                let line = lines.next().expect("ベクトルが足りない（ref_vectors を出し直す）");
                let f: Vec<&str> = line.split_whitespace().collect();
                assert_eq!(u64::from_str_radix(f[0], 16).unwrap(), seed, "line {line}");
                assert_eq!(f[1].parse::<usize>().unwrap(), len, "line {line}");
                let want = u64::from_str_radix(f[2], 16).unwrap();
                assert_eq!(hash_c(&k, &b), want, "seed {seed:#x} len {len}");
                n += 1;
            }
        }
        assert!(lines.next().is_none(), "ベクトルが余っている（ref_vectors を出し直す）");
        assert_eq!(n, 280);
    }
}
