//! 生成した核（`kernel.rs`）の差分テスト（P3 のゲート）。
//!
//! - 手書き試作の同名の関数（`lib.rs` の `fmix64` / `reduce` / `mulmod` / `horner`、`v2.rs` にあった
//!   `nh32_lane` / `nh_pair` / `ms` / limb の式。後者は切り替えで消したので下に写しを置く）と全一致すること
//! - Lean で証明した仕様（`LeanHash/Impl/Equiv.lean`）を u128 の素朴な計算で書いたものと一致すること
//!   （証明の言明を Rust 側から読み直す確認。証明があるので本来は不要）

use crate::kernel;
use crate::{splitmix64, P};

/// 切り替え前の `v2.rs` の手書き版（commit 64a56fa）の写し。
mod handwritten {
    const M32: u64 = 0xffff_ffff;
    pub const LIMB_MASK: u64 = (1 << 60) - 1;

    pub fn nh32_lane(v: u64, k: u64) -> u64 {
        let lo = v.wrapping_add(k) & M32;
        let hi = ((v >> 32) + (k >> 32)) & M32;
        lo * hi
    }

    pub fn nh_pair(a: u64, b: u64, ka: u64, kb: u64) -> u128 {
        (a.wrapping_add(ka) as u128) * (b.wrapping_add(kb) as u128)
    }

    pub fn ms(m: u128, x: u128) -> u64 {
        (m.wrapping_mul(x) >> 64) as u64
    }

    pub fn limbs(x: u64, y: u64) -> [u64; 3] {
        [x & LIMB_MASK, ((x >> 60) | (y << 4)) & LIMB_MASK, y >> 56]
    }
}

/// 境界の値を混ぜた乱数列。
fn samples(seed: u64, n: usize) -> Vec<u64> {
    let edges = [
        0,
        1,
        2,
        P - 1,
        P,
        P + 1,
        1 << 60,
        (1 << 61) - 2,
        1 << 61,
        (1 << 62) - 1,
        1 << 63,
        (1 << 63) - 1,
        0xffff_ffff,
        0x1_0000_0000,
        u64::MAX - 1,
        u64::MAX,
    ];
    let mut s = seed;
    let mut v: Vec<u64> = edges.to_vec();
    for _ in 0..n {
        let x = splitmix64(&mut s);
        // 上位ビットを落とした値も混ぜる（< p や < 2^60 の前提を満たす値を多めに）
        v.push(x);
        v.push(x >> (splitmix64(&mut s) % 64));
    }
    v
}

const N: usize = 200_000;

#[test]
fn fmix64_and_finish() {
    for x in samples(1, N) {
        assert_eq!(kernel::fmix64(x), crate::fmix64(x), "x {x:#x}");
        let fin = x.rotate_left(17) ^ 0x5555;
        assert_eq!(kernel::finish(x, fin), crate::fmix64(x ^ fin));
    }
}

#[test]
fn nh32_lane() {
    let xs = samples(2, N);
    for w in xs.windows(2) {
        let (v, k) = (w[0], w[1]);
        let got = kernel::nh32_lane(v, k);
        assert_eq!(got, handwritten::nh32_lane(v, k), "v {v:#x} k {k:#x}");
        // 仕様（Lean の nh32LaneK_eq）: pairVal (lane32 v) (lane32 k)
        let lo = ((v as u128 % (1 << 32)) + (k as u128 % (1 << 32))) % (1 << 32);
        let hi = ((v as u128 >> 32) + (k as u128 >> 32)) % (1 << 32);
        assert_eq!(got as u128, lo * hi);
    }
}

#[test]
fn nh_pair() {
    let xs = samples(3, N);
    for w in xs.windows(4) {
        let got = kernel::nh_pair(w[0], w[1], w[2], w[3]);
        assert_eq!(got, handwritten::nh_pair(w[0], w[1], w[2], w[3]));
    }
}

#[test]
fn reduce_mulmod_horner() {
    let xs = samples(4, N);
    let p = P as u128;
    for w in xs.windows(3) {
        // reduce は全 u64 で x mod p（Lean の reduceK_eq）。手書き版も同じ式
        assert_eq!(
            kernel::reduce(w[0]),
            (w[0] as u128 % p) as u64,
            "x {:#x}",
            w[0]
        );
        let (a, b, c) = (w[0] % P, w[1] % P, w[2]);
        assert_eq!(kernel::mulmod(a, b), crate::mulmod(a, b));
        assert_eq!(kernel::mulmod(a, b) as u128, a as u128 * b as u128 % p);
        // horner：仕様との一致は c < 2^63（hornerK_eq）。手書き版は `+ c` が素の加算なので、
        // c が大きいと debug ビルドで overflow の panic になる。比べるのは前提の範囲内だけ
        if c < 1 << 63 {
            assert_eq!(kernel::horner(a, b, c), crate::horner(a, b, c));
            assert_eq!(
                kernel::horner(a, b, c) as u128,
                (a as u128 * b as u128 + c as u128) % p
            );
        }
    }
}

#[test]
fn horner_precondition_is_needed() {
    // c ≥ 2^64 − p 付近では m + c が 2^64 を超えうる（Lean の仮定 c < 2^63 が要る例）
    let (h, r, c) = (P - 1, P - 1, u64::MAX);
    let spec = ((h as u128 * r as u128 + c as u128) % P as u128) as u64;
    assert_ne!(kernel::horner(h, r, c), spec);
}

#[test]
fn ms_and_limbs() {
    let xs = samples(5, N);
    for w in xs.windows(4) {
        let m = ((w[0] as u128) << 64 | w[1] as u128) | 1;
        let x = (w[2] as u128) << 64 | w[3] as u128;
        assert_eq!(kernel::ms(m, x), handwritten::ms(m, x));
        let (lx, ly) = (w[0], w[1]);
        let got = [kernel::limb0(lx), kernel::limb1(lx, ly), kernel::limb2(ly)];
        assert_eq!(got, handwritten::limbs(lx, ly));
        // 仕様（Lean の limbs）: v = x + 2^64·y の 60bit ずつ
        let v = lx as u128 | (ly as u128) << 64;
        let mask = (1u128 << 60) - 1;
        assert_eq!(
            got.map(|g| g as u128),
            [v & mask, (v >> 60) & mask, v >> 120]
        );
    }
}
