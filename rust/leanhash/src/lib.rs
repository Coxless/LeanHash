//! P0' 試作：NH 圧縮 → 多項式ハッシュ mod 2^61−1 → fmix64。
//!
//! **手書きの試作版**であり、HashIR から生成した検証済み実装ではない。
//! 速度と品質の当たりを付けるためのもので、差分テストの基準にもしない。
//!
//! 構造（入力 M、鍵 K = (k_nh, r, fin)）:
//! 1. M を 128 バイトのブロックに分割（最後の端数ブロックは 0 埋め、使う語数だけ処理）
//! 2. 各ブロックを NH で圧縮（`Nh64`: 64×64→128bit、`Nh32`: 32×32→64bit）
//! 3. NH 出力を 60bit の limb に分け、長さ（バイト数）を最後の係数として
//!    多項式ハッシュ mod p = 2^61−1（Horner 法、評価点 r）にかける
//! 4. 61bit の結果 h に 3bit を足して 64bit にし（`h << 3 | t`、単射）、fin と XOR して fmix64
//!
//! 衝突確率の上界（同じ鍵で x ≠ y、n はブロック数。証明は P2/P2.5 で Lean 上に作る）:
//! - `Nh64`: ε ≤ 2^-64 + (3n + 1) / p
//! - `Nh32`: ε ≤ 2^-32 + (2n + 1) / p

pub const P: u64 = (1 << 61) - 1;
pub const BLOCK_BYTES: usize = 128;
const BLOCK_WORDS: usize = BLOCK_BYTES / 8;
pub(crate) const LIMB_MASK: u64 = (1 << 60) - 1;

/// 鍵。NH 用 16 語（`Nh32` はこれを 32 個の u32 として使う）、多項式の評価点 r ∈ [0, p)、出力の白色化 fin。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Keys {
    pub nh: [u64; BLOCK_WORDS],
    pub r: u64,
    pub fin: u64,
}

pub(crate) fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

impl Keys {
    /// 試作用の鍵展開（splitmix64）。本番では OS 乱数から直接取る想定。
    pub fn from_seed(seed: u64) -> Self {
        let mut s = seed;
        let mut nh = [0u64; BLOCK_WORDS];
        for k in nh.iter_mut() {
            *k = splitmix64(&mut s);
        }
        // r は [0, p) から一様に（61bit を取り、p だけ棄却）
        let r = loop {
            let v = splitmix64(&mut s) >> 3;
            if v < P {
                break v;
            }
        };
        let fin = splitmix64(&mut s);
        Keys { nh, r, fin }
    }
}

// ---------------------------------------------------------------------------
// 有限体 GF(p), p = 2^61 − 1

/// x < 2^63 を [0, p) に縮約する。
#[inline(always)]
fn reduce(x: u64) -> u64 {
    let y = (x & P) + (x >> 61);
    if y >= P {
        y - P
    } else {
        y
    }
}

/// a, b < p のとき a·b mod p。
#[inline(always)]
pub fn mulmod(a: u64, b: u64) -> u64 {
    let t = (a as u128) * (b as u128); // < 2^122
    reduce(((t as u64) & P) + ((t >> 61) as u64)) // < 2^62
}

/// h < p、c < 2^60 のとき h·r + c mod p。
#[inline(always)]
pub(crate) fn horner(h: u64, r: u64, c: u64) -> u64 {
    reduce(mulmod(h, r) + c)
}

// ---------------------------------------------------------------------------
// 仕上げ段

/// MurmurHash3 の fmix64（全単射）。
#[inline(always)]
pub fn fmix64(mut x: u64) -> u64 {
    x ^= x >> 33;
    x = x.wrapping_mul(0xff51_afd7_ed55_8ccd);
    x ^= x >> 33;
    x = x.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    x ^= x >> 33;
    x
}

/// 多項式段の状態。h は Horner の累積、t は出力を 64bit に広げるための補助値。
struct Poly {
    h: u64,
    t: u64,
}

impl Poly {
    #[inline(always)]
    fn absorb128(&mut self, r: u64, acc: u128) {
        // 128bit を 60 + 60 + 8 bit の 3 係数に分ける（各係数 < 2^60 < p なので単射）
        let lo = acc as u64;
        let hi = (acc >> 64) as u64;
        self.h = horner(self.h, r, lo & LIMB_MASK);
        self.h = horner(self.h, r, ((lo >> 60) | (hi << 4)) & LIMB_MASK);
        self.h = horner(self.h, r, hi >> 56);
        self.t = self.t.wrapping_add(hi);
    }

    #[inline(always)]
    fn absorb64(&mut self, r: u64, acc: u64) {
        self.h = horner(self.h, r, acc & LIMB_MASK);
        self.h = horner(self.h, r, acc >> 60);
        self.t = self.t.wrapping_add(acc);
    }

    #[inline(always)]
    fn finish(self, k: &Keys, len: usize) -> u64 {
        let h = horner(self.h, k.r, len as u64);
        // h < 2^61 なので (h, t の上位 3bit) ↦ h<<3 | t>>61 は単射。
        // 衝突すれば h も衝突するので ε は変わらず、値域は約 2^64 になる。
        let v = (h << 3) | (self.t >> 61);
        fmix64(v ^ k.fin)
    }
}

#[inline(always)]
fn rd64(b: &[u8], i: usize) -> u64 {
    u64::from_le_bytes(b[i..i + 8].try_into().unwrap())
}

#[inline(always)]
fn rd32(b: &[u8], i: usize) -> u32 {
    u32::from_le_bytes(b[i..i + 4].try_into().unwrap())
}

/// 端数を 0 埋めした 128 バイトのブロック。
#[inline(always)]
fn pad_tail(tail: &[u8]) -> [u8; BLOCK_BYTES] {
    let mut buf = [0u8; BLOCK_BYTES];
    buf[..tail.len()].copy_from_slice(tail);
    buf
}

// ---------------------------------------------------------------------------
// NH64: 64bit 語、積は 128bit（NH の ε = 2^-64）

/// ブロック先頭 `pairs` 組だけ NH64 を計算する。
#[inline(always)]
fn nh64(k: &[u64; BLOCK_WORDS], b: &[u8], pairs: usize) -> u128 {
    let mut acc = 0u128;
    for i in 0..pairs {
        let a = rd64(b, 16 * i).wrapping_add(k[2 * i]);
        let c = rd64(b, 16 * i + 8).wrapping_add(k[2 * i + 1]);
        acc = acc.wrapping_add((a as u128) * (c as u128));
    }
    acc
}

pub fn hash_nh64(k: &Keys, data: &[u8]) -> u64 {
    let mut p = Poly { h: 0, t: 0 };
    let mut blocks = data.chunks_exact(BLOCK_BYTES);
    for b in &mut blocks {
        p.absorb128(k.r, nh64(&k.nh, b, BLOCK_WORDS / 2));
    }
    let tail = blocks.remainder();
    if !tail.is_empty() {
        let pairs = tail.len().div_ceil(16);
        p.absorb128(k.r, nh64(&k.nh, &pad_tail(tail), pairs));
    }
    p.finish(k, data.len())
}

// ---------------------------------------------------------------------------
// NH32: 32bit 語、積は 64bit（NH の ε = 2^-32）

#[inline(always)]
fn key32(k: &[u64; BLOCK_WORDS], j: usize) -> u32 {
    (k[j / 2] >> (32 * (j % 2))) as u32
}

#[inline(always)]
fn nh32(k: &[u64; BLOCK_WORDS], b: &[u8], pairs: usize) -> u64 {
    let mut acc = 0u64;
    for i in 0..pairs {
        let a = rd32(b, 8 * i).wrapping_add(key32(k, 2 * i));
        let c = rd32(b, 8 * i + 4).wrapping_add(key32(k, 2 * i + 1));
        acc = acc.wrapping_add((a as u64) * (c as u64));
    }
    acc
}

pub fn hash_nh32(k: &Keys, data: &[u8]) -> u64 {
    let mut p = Poly { h: 0, t: 0 };
    let mut blocks = data.chunks_exact(BLOCK_BYTES);
    for b in &mut blocks {
        p.absorb64(k.r, nh32(&k.nh, b, BLOCK_BYTES / 8));
    }
    let tail = blocks.remainder();
    if !tail.is_empty() {
        let pairs = tail.len().div_ceil(8);
        p.absorb64(k.r, nh32(&k.nh, &pad_tail(tail), pairs));
    }
    p.finish(k, data.len())
}

pub mod v2;

#[cfg(test)]
mod tests {
    use super::*;

    fn fmix64_inv(mut x: u64) -> u64 {
        // 逆関数（P1 で Lean に移す性質の手元確認）
        const INV1: u64 = 0x4f74_430c_22a5_4005; // 0xff51afd7ed558ccd の逆元
        const INV2: u64 = 0x9cb4_b2f8_1293_37db; // 0xc4ceb9fe1a85ec53 の逆元
        let unxs = |x: u64| x ^ (x >> 33); // 33 > 32 なので xorshift 33 は自己逆
        x = unxs(x);
        x = x.wrapping_mul(INV2);
        x = unxs(x);
        x = x.wrapping_mul(INV1);
        unxs(x)
    }

    #[test]
    fn mul_inverses() {
        assert_eq!(0xff51_afd7_ed55_8ccdu64.wrapping_mul(0x4f74_430c_22a5_4005), 1);
        assert_eq!(0xc4ce_b9fe_1a85_ec53u64.wrapping_mul(0x9cb4_b2f8_1293_37db), 1);
    }

    /// Lean の仕様（`LeanHash/Spec/Fmix.lean` の `example`）と同じテストベクトル。
    #[test]
    fn fmix64_matches_lean_vectors() {
        let v: [(u64, u64); 5] = [
            (0x0000000000000000, 0x0000000000000000),
            (0x0000000000000001, 0xb456bcfc34c2cb2c),
            (0x8000000000000000, 0x8f780810af31a493),
            (0x0123456789abcdef, 0x87cbfbfe89022cea),
            (0xffffffffffffffff, 0x64b5720b4b825f21),
        ];
        for (x, y) in v {
            assert_eq!(fmix64(x), y);
            assert_eq!(fmix64_inv(y), x);
        }
    }

    #[test]
    fn fmix64_roundtrip() {
        let mut s = 1u64;
        for _ in 0..10_000 {
            let x = splitmix64(&mut s);
            assert_eq!(fmix64_inv(fmix64(x)), x);
        }
    }

    #[test]
    fn mulmod_matches_naive() {
        let mut s = 7u64;
        let edge = [0, 1, 2, P - 1, P - 2, 1 << 60, (1 << 60) - 1];
        for &a in &edge {
            for &b in &edge {
                assert_eq!(mulmod(a, b) as u128, (a as u128 * b as u128) % P as u128);
            }
        }
        for _ in 0..100_000 {
            let a = splitmix64(&mut s) % P;
            let b = splitmix64(&mut s) % P;
            assert_eq!(mulmod(a, b) as u128, (a as u128 * b as u128) % P as u128);
        }
    }

    #[test]
    fn horner_stays_in_field() {
        let mut s = 3u64;
        for _ in 0..100_000 {
            let h = splitmix64(&mut s) % P;
            let r = splitmix64(&mut s) % P;
            let c = splitmix64(&mut s) & LIMB_MASK;
            let v = horner(h, r, c);
            assert!(v < P);
            assert_eq!(v as u128, (h as u128 * r as u128 + c as u128) % P as u128);
        }
    }

    #[test]
    fn keys_r_in_field() {
        for seed in 0..1000 {
            assert!(Keys::from_seed(seed).r < P);
        }
    }

    #[test]
    fn padding_and_length_are_distinguished() {
        let k = Keys::from_seed(42);
        for f in [hash_nh64, hash_nh32] {
            let mut seen = std::collections::HashSet::new();
            // 0 埋めと見分けがつかない入力（"", "\0", "\0\0", …）が衝突しないこと
            for n in 0..300 {
                assert!(seen.insert(f(&k, &vec![0u8; n])), "len {n}");
            }
        }
    }

    #[test]
    fn seed_changes_output() {
        let a = Keys::from_seed(1);
        let b = Keys::from_seed(2);
        let msg = b"leanhash";
        assert_ne!(hash_nh64(&a, msg), hash_nh64(&b, msg));
        assert_ne!(hash_nh32(&a, msg), hash_nh32(&b, msg));
    }

    /// 鍵が漏れると衝突は作れる（ε-AU は「鍵が入力と独立」が前提であることの確認）。
    /// 2 語目を −k1 にすると積が 0 になり、1 語目が何でも同じ値になる。
    #[test]
    fn leaked_key_gives_collisions() {
        let k = Keys::from_seed(99);
        let w1 = 0u64.wrapping_sub(k.nh[1]);
        let mut x = [0u8; 16];
        let mut y = [0u8; 16];
        x[..8].copy_from_slice(&1u64.to_le_bytes());
        y[..8].copy_from_slice(&2u64.to_le_bytes());
        x[8..].copy_from_slice(&w1.to_le_bytes());
        y[8..].copy_from_slice(&w1.to_le_bytes());
        assert_eq!(hash_nh64(&k, &x), hash_nh64(&k, &y));

        let w1 = 0u32.wrapping_sub(key32(&k.nh, 1));
        let mut x = [0u8; 8];
        let mut y = [0u8; 8];
        x[..4].copy_from_slice(&1u32.to_le_bytes());
        y[..4].copy_from_slice(&2u32.to_le_bytes());
        x[4..].copy_from_slice(&w1.to_le_bytes());
        y[4..].copy_from_slice(&w1.to_le_bytes());
        assert_eq!(hash_nh32(&k, &x), hash_nh32(&k, &y));
    }
}
