/-
P2 の核心となる整数の補題。NH の 1 組で、1 語目の値が違う (a ≠ a') とき、
2 語目の鍵を変えると差 a·x − a'·x' (mod W²) が必ず変わることを示すための不等式評価。
W が 2 の累乗であることは使わない。
-/
import Mathlib

namespace LeanHash.Props

/-- d' = d − W の場合：a·d − a'·d' は W² の倍数にならない。 -/
theorem core_shift (W a a' d : ℤ) (ha0 : 0 ≤ a) (haW : a < W) (hb0 : 0 ≤ a') (hbW : a' < W)
    (hne : a ≠ a') (hd0 : 0 < d) (hdW : d < W) (s : ℤ)
    (hs : a * d - a' * (d - W) = W ^ 2 * s) : False := by
  have hW : 0 < W := by omega
  -- s は 0 か 1
  have hlo : -(W ^ 2) < a * d - a' * (d - W) := by nlinarith
  have hhi : a * d - a' * (d - W) < 2 * W ^ 2 := by nlinarith
  have hs0 : 0 ≤ s := by
    by_contra h; push Not at h
    have : W ^ 2 * s ≤ -(W ^ 2) := by nlinarith
    linarith
  have hs1 : s ≤ 1 := by
    by_contra h; push Not at h
    have : 2 * W ^ 2 ≤ W ^ 2 * s := by nlinarith
    linarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- a < a'
    have : s = 0 ∨ s = 1 := by omega
    rcases this with rfl | rfl
    · -- (a' − a)·d = a'·W、ところが (a' − a)·d < a'·W
      nlinarith
    · nlinarith
  · have : s = 0 ∨ s = 1 := by omega
    rcases this with rfl | rfl
    · nlinarith
    · -- (a − a')·d = W(W − a')、ところが a − a' < W − a'
      nlinarith

/-- 補題の本体：|d|, |d'| < W、d ≡ d' (mod W)、W² ∣ a·d − a'·d'、a ≠ a' なら d = 0。 -/
theorem core (W a a' d d' : ℤ) (ha0 : 0 ≤ a) (haW : a < W) (hb0 : 0 ≤ a') (hbW : a' < W)
    (hne : a ≠ a') (hd : -W < d) (hd' : d < W) (he : -W < d') (he' : d' < W)
    (hmod : W ∣ d' - d) (hdvd : W ^ 2 ∣ a * d - a' * d') : d = 0 := by
  have hW : 0 < W := by omega
  obtain ⟨t, ht⟩ := hmod
  obtain ⟨s, hs⟩ := hdvd
  have ht1 : -1 ≤ t := by nlinarith
  have ht2 : t ≤ 1 := by nlinarith
  have : t = -1 ∨ t = 0 ∨ t = 1 := by omega
  rcases this with rfl | rfl | rfl
  · -- d' = d − W
    have hdd : d' = d - W := by linarith
    subst hdd
    exact (core_shift W a a' d ha0 haW hb0 hbW hne (by omega) hd' s hs).elim
  · -- d' = d
    have hdd : d' = d := by linarith
    subst hdd
    by_contra hd0
    have hab : a - a' ≠ 0 := sub_ne_zero.mpr hne
    have hprod : (a - a') * d' = W ^ 2 * s := by linarith
    have hs0 : s = 0 := by
      have h1 : |a - a'| < W := by rw [abs_lt]; constructor <;> linarith
      have h2 : |d'| < W := by rw [abs_lt]; constructor <;> linarith
      have h3 : |(a - a') * d'| < W ^ 2 := by
        rw [abs_mul, sq]; exact mul_lt_mul'' h1 h2 (abs_nonneg _) (abs_nonneg _)
      rw [hprod, abs_mul, abs_of_pos (by positivity : (0:ℤ) < W ^ 2)] at h3
      have : |s| < 1 := by
        by_contra h; push Not at h; nlinarith [sq_nonneg W]
      rcases abs_lt.mp this with ⟨h4, h5⟩; omega
    rw [hs0, mul_zero] at hprod
    rcases mul_eq_zero.mp hprod with h | h
    · exact hab h
    · exact hd0 h
  · -- d' = d + W：符号を反転すると d' = d − W の場合に帰着
    have hdd : d' = d + W := by linarith
    subst hdd
    exact (core_shift W a a' (-d) ha0 haW hb0 hbW hne (by omega) (by omega) (-s)
      (by linarith)).elim

end LeanHash.Props
