/-
P2 残り 2：v2c の 1KB 以下の経路で、バイト列を NH の組（レーン）の並びに変える仕様。

`rust/leanhash/src/v2.rs` の `nh_partial`（経路 A、L ≤ 32）と `nh32x2_partial`（経路 B、33 ≤ L ≤ 1024）を写したもの。
語は little-endian。ない組は `none`（和に何も足さない）。長さの組は長さによらず最後の位置。

経路 A（NH64、W = 2⁶⁴、組 65 個 = 鍵 130 語）:
- 組 0: L = 0 ならなし。1〜3 は (b₀ + 2⁸·b_{L/2} + 2¹⁶·b_{L−1}, 0)、4〜7 は (rd32 0, rd32 (L−4))、
  8〜16 は (rd64 0, rd64 (L−8))、17〜32 は (rd64 0, rd64 8)
- 組 1: 17〜32 のときだけ (rd64 (L−16), rd64 (L−8))（末尾 16 バイトを重ねて読む）
- 組 64: (L, 0)

経路 B（NH32 の Toeplitz 2 本、W = 2³²、レーン 129 個 = 鍵レーン 130 個）:
- レーン i < ⌈L/8⌉ − 1: 8i バイト目からの 8 バイト（下位 4 バイト, 上位 4 バイト）
- レーン ⌈L/8⌉ − 1: 末尾 8 バイト（重ねて読む）
- レーン 128: (L, 0)
-/
import Mathlib

namespace LeanHash.Spec

open Finset

/-- バイト列。 -/
abbrev Bytes := List (Fin 256)

/-- i バイト目の値（範囲外は 0。仕様では範囲外は読まない）。 -/
def byteAt (s : Bytes) (i : ℕ) : ℕ := (s.getD i 0 : Fin 256)

/-- o バイト目から k バイトを little-endian で読む。 -/
def readLE (k : ℕ) (s : Bytes) (o : ℕ) : ℕ := ∑ j ∈ range k, byteAt s (o + j) * 256 ^ j

/-- b ビット語に切り詰める（読んだ値は最初から範囲内なので、実際には何も起きない）。 -/
def wd (b n : ℕ) : Fin (2 ^ b) := ⟨n % 2 ^ b, Nat.mod_lt _ (by positivity)⟩

/-- 経路 A の短い入力（1〜16 バイト）の組 0。 -/
def shortPair (s : Bytes) : ℕ × ℕ :=
  let L := s.length
  if 8 ≤ L then (readLE 8 s 0, readLE 8 s (L - 8))
  else if 4 ≤ L then (readLE 4 s 0, readLE 4 s (L - 4))
  else (byteAt s 0 + 256 * byteAt s (L / 2) + 65536 * byteAt s (L - 1), 0)

/-- 経路 A（L ≤ 32）：NH64 の組の並び。 -/
def msgA (s : Bytes) : Fin 65 → Option (Fin (2 ^ 64) × Fin (2 ^ 64)) := fun i =>
  let L := s.length
  if i.val = 64 then some (wd 64 L, wd 64 0)
  else if i.val = 0 then
    if L = 0 then none
    else if L ≤ 16 then some (wd 64 (shortPair s).1, wd 64 (shortPair s).2)
    else some (wd 64 (readLE 8 s 0), wd 64 (readLE 8 s 8))
  else if i.val = 1 ∧ 16 < L then some (wd 64 (readLE 8 s (L - 16)), wd 64 (readLE 8 s (L - 8)))
  else none

/-- 経路 B のデータレーンの数 ⌈L/8⌉。 -/
def lanesB (L : ℕ) : ℕ := (L + 7) / 8

/-- 経路 B（33 ≤ L ≤ 1024）：NH32 のレーンの並び。 -/
def msgB (s : Bytes) : Fin 129 → Option (Fin (2 ^ 32) × Fin (2 ^ 32)) := fun i =>
  let L := s.length
  if i.val = 128 then some (wd 32 L, wd 32 0)
  else if i.val + 1 < lanesB L then some (wd 32 (readLE 4 s (8 * i.val)), wd 32 (readLE 4 s (8 * i.val + 4)))
  else if i.val + 1 = lanesB L then some (wd 32 (readLE 4 s (L - 8)), wd 32 (readLE 4 s (L - 4)))
  else none

/-! ### 読み取りの性質 -/

theorem byteAt_lt (s : Bytes) (i : ℕ) : byteAt s i < 256 := (s.getD i 0).isLt

theorem readLE_succ (k : ℕ) (s : Bytes) (o : ℕ) :
    readLE (k + 1) s o = byteAt s o + 256 * readLE k s (o + 1) := by
  unfold readLE
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one, add_zero, pow_succ]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show o + (j + 1) = o + 1 + j by ring]
  ring

theorem readLE_lt (k : ℕ) (s : Bytes) (o : ℕ) : readLE k s o < 256 ^ k := by
  induction k generalizing o with
  | zero => simp [readLE]
  | succ k ih =>
    rw [readLE_succ, pow_succ]
    have := ih (o + 1)
    have := byteAt_lt s o
    omega

/-- 読んだ値が同じなら、その範囲のバイトは全部同じ。 -/
theorem readLE_inj {k : ℕ} {s s' : Bytes} {o o' : ℕ} (h : readLE k s o = readLE k s' o') :
    ∀ j < k, byteAt s (o + j) = byteAt s' (o' + j) := by
  induction k generalizing o o' with
  | zero => intro j hj; omega
  | succ k ih =>
    rw [readLE_succ, readLE_succ] at h
    have h0 := byteAt_lt s o
    have h0' := byteAt_lt s' o'
    have hb : byteAt s o = byteAt s' o' := by omega
    have hr : readLE k s (o + 1) = readLE k s' (o' + 1) := by omega
    intro j hj
    rcases j with _ | j
    · simpa using hb
    · have := ih hr j (by omega)
      rwa [show o + 1 + j = o + (j + 1) by ring, show o' + 1 + j = o' + (j + 1) by ring] at this

theorem wd_inj {b n m : ℕ} (hn : n < 2 ^ b) (hm : m < 2 ^ b) (h : wd b n = wd b m) : n = m := by
  have := congrArg Fin.val h
  simpa [wd, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] using this

theorem readLE8_lt (s : Bytes) (o : ℕ) : readLE 8 s o < 2 ^ 64 :=
  (readLE_lt 8 s o).trans_eq (by norm_num)

theorem readLE4_lt (s : Bytes) (o : ℕ) : readLE 4 s o < 2 ^ 32 :=
  (readLE_lt 4 s o).trans_eq (by norm_num)

theorem readLE4_lt64 (s : Bytes) (o : ℕ) : readLE 4 s o < 2 ^ 64 :=
  (readLE4_lt s o).trans (by norm_num)

/-- 同じ長さで、各バイトが同じなら同じ列。 -/
theorem bytes_ext {s s' : Bytes} (hlen : s.length = s'.length)
    (h : ∀ i < s.length, byteAt s i = byteAt s' i) : s = s' := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have := h i h1
  simp only [byteAt, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  exact Fin.ext this

/-- 64bit 語を 2 回読んで同じなら、両方の範囲のバイトが同じ。 -/
theorem pair64_bytes {s s' : Bytes} {o1 o2 o1' o2' : ℕ}
    (h : some (wd 64 (readLE 8 s o1), wd 64 (readLE 8 s o2)) =
      some (wd 64 (readLE 8 s' o1'), wd 64 (readLE 8 s' o2'))) :
    (∀ j < 8, byteAt s (o1 + j) = byteAt s' (o1' + j)) ∧
      (∀ j < 8, byteAt s (o2 + j) = byteAt s' (o2' + j)) := by
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨readLE_inj (wd_inj (readLE8_lt _ _) (readLE8_lt _ _) h.1),
    readLE_inj (wd_inj (readLE8_lt _ _) (readLE8_lt _ _) h.2)⟩

/-! ### 経路 A の単射性 -/

/-- **経路 A：同じ長さ（≤ 32）なら、組の並びからバイト列が決まる。** -/
theorem msgA_inj {s s' : Bytes} (hlen : s.length = s'.length) (h32 : s.length ≤ 32)
    (h : msgA s = msgA s') : s = s' := by
  apply bytes_ext hlen
  intro i hi
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [msgA, ← hlen, Fin.val_zero, Fin.val_one] at h0 h1
  set L := s.length with hL
  by_cases hL16 : L ≤ 16
  · simp only [show L ≠ 0 by omega, ite_false, hL16, ite_true, show ¬ (0 = 64) by omega] at h0
    simp only [shortPair, ← hL, ← hlen] at h0
    by_cases h8 : 8 ≤ L
    · simp only [h8, ite_true] at h0
      obtain ⟨ha, hb⟩ := pair64_bytes h0
      by_cases hi8 : i < 8
      · simpa using ha i hi8
      · have := hb (i - (L - 8)) (by omega)
        rwa [show L - 8 + (i - (L - 8)) = i by omega] at this
    by_cases h4 : 4 ≤ L
    · simp only [h8, h4, ite_true, ite_false] at h0
      simp only [Option.some.injEq, Prod.mk.injEq] at h0
      have ha := readLE_inj (wd_inj (readLE4_lt64 _ _) (readLE4_lt64 _ _) h0.1)
      have hb := readLE_inj (wd_inj (readLE4_lt64 _ _) (readLE4_lt64 _ _) h0.2)
      by_cases hi4 : i < 4
      · simpa using ha i hi4
      · have := hb (i - (L - 4)) (by omega)
        rwa [show L - 4 + (i - (L - 4)) = i by omega] at this
    · simp only [h8, h4, ite_false] at h0
      simp only [Option.some.injEq, Prod.mk.injEq] at h0
      have hlt : ∀ (t : Bytes), byteAt t 0 + 256 * byteAt t (L / 2) + 65536 * byteAt t (L - 1) <
          2 ^ 64 := fun t => by
        have := byteAt_lt t 0; have := byteAt_lt t (L / 2); have := byteAt_lt t (L - 1); omega
      have e := wd_inj (hlt s) (hlt s') h0.1
      have := byteAt_lt s 0; have := byteAt_lt s (L / 2); have := byteAt_lt s (L - 1)
      have := byteAt_lt s' 0; have := byteAt_lt s' (L / 2); have := byteAt_lt s' (L - 1)
      have e0 : byteAt s 0 = byteAt s' 0 := by omega
      have e1 : byteAt s (L / 2) = byteAt s' (L / 2) := by omega
      have e2 : byteAt s (L - 1) = byteAt s' (L - 1) := by omega
      rcases (by omega : i = 0 ∨ i = L / 2 ∨ i = L - 1) with rfl | rfl | rfl <;> assumption
  · simp only [show L ≠ 0 by omega, ite_false, hL16, show ¬ (0 = 64) by omega] at h0
    simp only [show ¬ (1 = 64) by omega, show ¬ (1 = 0) by omega, true_and,
      show 16 < L by omega, ite_true, ite_false] at h1
    obtain ⟨ha, hb⟩ := pair64_bytes h0
    obtain ⟨hc, hd⟩ := pair64_bytes h1
    by_cases hi8 : i < 8
    · simpa using ha i hi8
    by_cases hi16 : i < 16
    · have := hb (i - 8) (by omega)
      rwa [show 8 + (i - 8) = i by omega] at this
    by_cases hi' : i < L - 8
    · have := hc (i - (L - 16)) (by omega)
      rwa [show L - 16 + (i - (L - 16)) = i by omega] at this
    · have := hd (i - (L - 8)) (by omega)
      rwa [show L - 8 + (i - (L - 8)) = i by omega] at this

/-- 経路 A の組の有無は長さだけで決まる。 -/
theorem msgA_isSome {s s' : Bytes} (hlen : s.length = s'.length) (i : Fin 65) :
    (msgA s i).isSome = (msgA s' i).isSome := by
  unfold msgA
  simp only [hlen]
  split_ifs <;> simp

/-! ### 経路 B の単射性 -/

/-- **経路 B：同じ長さ（8 ≤ L ≤ 1024）なら、レーンの並びからバイト列が決まる。** -/
theorem msgB_inj {s s' : Bytes} (hlen : s.length = s'.length) (h8 : 8 ≤ s.length)
    (h1024 : s.length ≤ 1024) (h : msgB s = msgB s') : s = s' := by
  apply bytes_ext hlen
  intro i hi
  set L := s.length with hL
  have hlanes : lanesB L ≤ 128 := by unfold lanesB; omega
  have lane_bytes : ∀ (k : Fin 129) (o1 o2 : ℕ),
      msgB s k = some (wd 32 (readLE 4 s o1), wd 32 (readLE 4 s o2)) →
      msgB s' k = some (wd 32 (readLE 4 s' o1), wd 32 (readLE 4 s' o2)) →
      (∀ j < 4, byteAt s (o1 + j) = byteAt s' (o1 + j)) ∧
        (∀ j < 4, byteAt s (o2 + j) = byteAt s' (o2 + j)) := by
    intro k o1 o2 e e'
    have hk := congrFun h k
    rw [e, e'] at hk
    simp only [Option.some.injEq, Prod.mk.injEq] at hk
    exact ⟨readLE_inj (wd_inj (readLE4_lt _ _) (readLE4_lt _ _) hk.1),
      readLE_inj (wd_inj (readLE4_lt _ _) (readLE4_lt _ _) hk.2)⟩
  by_cases hq : i / 8 + 1 < lanesB L
  · -- 途中のレーン i/8 が i を含む
    have hk : (i / 8 : ℕ) < 129 := by omega
    obtain ⟨ha, hb⟩ := lane_bytes ⟨i / 8, hk⟩ (8 * (i / 8)) (8 * (i / 8) + 4)
      (by simp only [msgB, ← hL, show i / 8 ≠ 128 by omega, hq, ↓reduceIte])
      (by simp only [msgB, ← hlen, show i / 8 ≠ 128 by omega, hq, ↓reduceIte])
    by_cases hlo : i % 8 < 4
    · have := ha (i % 8) hlo
      rwa [show 8 * (i / 8) + i % 8 = i by omega] at this
    · have := hb (i % 8 - 4) (by omega)
      rwa [show 8 * (i / 8) + 4 + (i % 8 - 4) = i by omega] at this
  · -- 最後のレーン（末尾 8 バイト）が i を含む
    have hk : lanesB L - 1 < 129 := by omega
    have hlast : lanesB L - 1 + 1 = lanesB L := by unfold lanesB; omega
    obtain ⟨ha, hb⟩ := lane_bytes ⟨lanesB L - 1, hk⟩ (L - 8) (L - 4)
      (by simp only [msgB, ← hL, show lanesB L - 1 ≠ 128 by omega, hlast, lt_irrefl, ↓reduceIte])
      (by simp only [msgB, ← hlen, show lanesB L - 1 ≠ 128 by omega, hlast, lt_irrefl, ↓reduceIte])
    have hiL : L - 8 ≤ i := by unfold lanesB at hq; omega
    by_cases hlo : i < L - 4
    · have := ha (i - (L - 8)) (by omega)
      rwa [show L - 8 + (i - (L - 8)) = i by omega] at this
    · have := hb (i - (L - 4)) (by omega)
      rwa [show L - 4 + (i - (L - 4)) = i by omega] at this

/-- 経路 B のレーンの有無は長さだけで決まる。 -/
theorem msgB_isSome {s s' : Bytes} (hlen : s.length = s'.length) (i : Fin 129) :
    (msgB s i).isSome = (msgB s' i).isSome := by
  unfold msgB
  simp only [hlen]
  split_ifs <;> simp

end LeanHash.Spec
