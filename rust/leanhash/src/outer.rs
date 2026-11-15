//! P3.5：外側の処理のうち、Aeneas で Lean に抽出して検証する部分。
//!
//! safe Rust だけで、Aeneas の対応範囲（`while` ループ、スライスの添字、算術）で書く。
//! 抽出: `charon cargo --preset=aeneas --start-from leanhash::outer` → `aeneas -backend lean`
//! （手順と結果は docs/journal/2026-11-15-p35-aeneas.md）。
//! 抽出した Lean の関数が、仕様と一致を証明済みの参照実装（`LeanHash/Impl/Outer.lean`）と一致することを
//! `LeanHash/Aeneas/OuterProof.lean` で示す。

use crate::kernel::nh32_lane;

/// i バイト目から 8 バイトを little-endian で読む（`v2::rd64` と同じ値）。
/// 先に 8 バイトを切り出すので、添字の検査は 1 回にまとまり、OR とシフトは 1 回の読み出しに最適化される。
#[inline(always)]
pub fn rd64(b: &[u8], i: usize) -> u64 {
    let c = &b[i..i + 8];
    (c[0] as u64)
        | (c[1] as u64) << 8
        | (c[2] as u64) << 16
        | (c[3] as u64) << 24
        | (c[4] as u64) << 32
        | (c[5] as u64) << 40
        | (c[6] as u64) << 48
        | (c[7] as u64) << 56
}

/// NH32×2 のレーン `start..lanes` をスカラーで (s1, s2) に足す。レーン i は 8i バイト目から、
/// 最後のレーン（i + 1 = lanes）は末尾 8 バイト（重ねて読む）。1 本目は鍵 i、2 本目は鍵 i + 1。
/// `v2::nh32x2_partial` のスカラーのループ（AVX2 がなければ全レーン、あれば 4 の倍数より後のレーン）。
#[inline(always)]
pub fn nh32x2_lanes(k: &[u64; 130], b: &[u8], lanes: usize, start: usize, s1: u64, s2: u64) -> (u64, u64) {
    let len = b.len();
    let mut s1 = s1;
    let mut s2 = s2;
    let mut i = start;
    while i < lanes {
        let v = if i + 1 == lanes { rd64(b, len - 8) } else { rd64(b, 8 * i) };
        s1 = s1.wrapping_add(nh32_lane(v, k[i]));
        s2 = s2.wrapping_add(nh32_lane(v, k[i + 1]));
        i += 1;
    }
    (s1, s2)
}

/// 長さ 8..=1024 の端数の NH32×2（スカラー版の全体）。
#[inline(always)]
pub fn nh32x2_partial_scalar(k: &[u64; 130], b: &[u8]) -> (u64, u64) {
    nh32x2_lanes(k, b, b.len().div_ceil(8), 0, 0, 0)
}
