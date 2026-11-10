/-
P2.5：v2c の 1KB より長い経路（`rust/leanhash/src/v2.rs` の `hash_long_b`）で、
バイト列を NH32×2 のレーンの並び（ブロックごと）に変える仕様。

L > 1024。完全ブロック nb = ⌊L/1024⌋ 個と、最後のブロック 1 個（計 `nBlk L = nb + 1` 個）:
- 完全ブロック j < nb：バイト [1024j, 1024j + 1024) を経路 B と同じ読み方（`msgB`）で 128 レーン。長さレーンなし
- 最後のブロック：レーン 128 に長さレーン（L の下位 32bit, 上位 32bit）。
  rem = L mod 1024 > 0 なら、末尾 max(rem, 8) バイト（`tail`。直前のブロックと重なってよい）を `msgB` で読む。
  rem = 0 ならデータのレーンはない
-/
import LeanHash.Spec.Encode

namespace LeanHash.Spec

open Finset

/-- j 番目の完全ブロック（1024 バイト）。 -/
def blk (s : Bytes) (j : ℕ) : Bytes := (s.drop (1024 * j)).take 1024

/-- 最後のブロックで読むバイト数 max(L mod 1024, 8)。 -/
def tailLen (L : ℕ) : ℕ := max (L % 1024) 8

/-- 最後のブロックで読む末尾。 -/
def tail (s : Bytes) : Bytes := s.drop (s.length - tailLen s.length)

/-- 長さレーン（Rust の `nh32_lane(len as u64, ·)`：下位 32bit と上位 32bit）。 -/
def lenLane (L : ℕ) : Fin (2 ^ 32) × Fin (2 ^ 32) := (wd 32 L, wd 32 (L / 2 ^ 32))

/-- 完全ブロックのレーン（レーン 128 はなし）。 -/
def msgFull (s : Bytes) (j : ℕ) : Fin 129 → Option (Fin (2 ^ 32) × Fin (2 ^ 32)) := fun i =>
  if i.val = 128 then none else msgB (blk s j) i

/-- 最後のブロックのレーン。 -/
def msgLast (s : Bytes) : Fin 129 → Option (Fin (2 ^ 32) × Fin (2 ^ 32)) := fun i =>
  if i.val = 128 then some (lenLane s.length)
  else if s.length % 1024 = 0 then none
  else msgB (tail s) i

/-- NH の出力の数（ブロック数）。 -/
def nBlk (L : ℕ) : ℕ := L / 1024 + 1

/-- j 番目のブロックのレーン。 -/
def msgL (s : Bytes) (j : ℕ) : Fin 129 → Option (Fin (2 ^ 32) × Fin (2 ^ 32)) :=
  if j < s.length / 1024 then msgFull s j else msgLast s

/-! ### 切り出しとバイト -/

theorem byteAt_drop (s : Bytes) (d i : ℕ) : byteAt (s.drop d) i = byteAt s (d + i) := by
  simp [byteAt, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem byteAt_take (s : Bytes) {n i : ℕ} (h : i < n) : byteAt (s.take n) i = byteAt s i := by
  simp [byteAt, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem length_blk (s : Bytes) {j : ℕ} (hj : j < s.length / 1024) : (blk s j).length = 1024 := by
  simp only [blk, List.length_take, List.length_drop]
  omega

theorem length_tail (s : Bytes) (h8 : 8 ≤ s.length) : (tail s).length = tailLen s.length := by
  simp only [tail, List.length_drop, tailLen]
  omega

/-- 長さ 1024 以下・8 以上の同じ長さの 2 つの列で、レーン 128 以外が同じなら列も同じ。 -/
theorem eq_of_msgB_lt128 {b b' : Bytes} (hlen : b.length = b'.length) (h8 : 8 ≤ b.length)
    (h1024 : b.length ≤ 1024) (h : ∀ i : Fin 129, i.val ≠ 128 → msgB b i = msgB b' i) : b = b' := by
  refine msgB_inj hlen h8 h1024 (funext fun i => ?_)
  by_cases hi : i.val = 128
  · simp only [msgB, hi, ↓reduceIte, hlen]
  · exact h i hi

/-! ### 単射性と有無 -/

/-- **長い経路：同じ長さ（L > 1024）なら、全ブロックのレーンの並びからバイト列が決まる。** -/
theorem msgL_inj {s s' : Bytes} (hlen : s.length = s'.length) (h1024 : 1024 < s.length)
    (h : ∀ j < nBlk s.length, msgL s j = msgL s' j) : s = s' := by
  apply bytes_ext hlen
  intro i hi
  set L := s.length with hL
  by_cases hfull : i < 1024 * (L / 1024)
  · -- 完全ブロック i / 1024
    have hj : i / 1024 < L / 1024 := by omega
    have hj' : i / 1024 < s'.length / 1024 := by rw [← hlen]; exact hj
    have e := h (i / 1024) (by unfold nBlk; omega)
    simp only [msgL, ← hL, hj, hj', ↓reduceIte] at e
    have hb : blk s (i / 1024) = blk s' (i / 1024) := by
      refine eq_of_msgB_lt128 (by rw [length_blk _ hj, length_blk _ hj'])
        (by rw [length_blk _ hj]; omega) (by rw [length_blk _ hj]) fun k hk => ?_
      have := congrFun e k
      simpa only [msgFull, hk, ↓reduceIte] using this
    have := congrArg (fun b => byteAt b (i % 1024)) hb
    simp only [blk] at this
    rw [byteAt_take _ (Nat.mod_lt _ (by norm_num)), byteAt_take _ (Nat.mod_lt _ (by norm_num)),
      byteAt_drop, byteAt_drop, show 1024 * (i / 1024) + i % 1024 = i by omega] at this
    exact this
  · -- 最後のブロック（末尾）
    have hrem : L % 1024 ≠ 0 := by omega
    have hrem' : s'.length % 1024 ≠ 0 := by rw [← hlen]; exact hrem
    have e := h (L / 1024) (by unfold nBlk; omega)
    simp only [msgL, ← hL, lt_irrefl, ↓reduceIte, show ¬ (L / 1024 < s'.length / 1024) by omega] at e
    have hT : 8 ≤ L := by omega
    have ht : tail s = tail s' := by
      refine eq_of_msgB_lt128
        (by rw [length_tail _ hT, length_tail _ (by omega)]; exact congrArg tailLen hlen)
        (by rw [length_tail _ hT]; unfold tailLen; omega)
        (by rw [length_tail _ hT]; unfold tailLen; omega) fun k hk => ?_
      have := congrFun e k
      simpa only [msgLast, hk, ↓reduceIte, ← hL, hrem, hrem'] using this
    have hiT : L - tailLen L ≤ i := by unfold tailLen; omega
    have := congrArg (fun b => byteAt b (i - (L - tailLen L))) ht
    simp only [tail, ← hL, ← hlen] at this
    rw [byteAt_drop, byteAt_drop, show L - tailLen L + (i - (L - tailLen L)) = i by omega] at this
    exact this

/-- 長い経路のレーンの有無は長さだけで決まる。 -/
theorem msgL_isSome {s s' : Bytes} (hlen : s.length = s'.length) (h8 : 8 ≤ s.length) (j : ℕ)
    (i : Fin 129) : (msgL s j i).isSome = (msgL s' j i).isSome := by
  unfold msgL
  rw [← hlen]
  split_ifs with hj
  · unfold msgFull
    split_ifs
    · rfl
    · exact msgB_isSome (by rw [length_blk _ hj, length_blk _ (hlen ▸ hj)]) i
  · unfold msgLast
    rw [← hlen]
    split_ifs
    · rfl
    · rfl
    · exact msgB_isSome (by rw [length_tail _ h8, length_tail _ (by omega), hlen]) i

end LeanHash.Spec
