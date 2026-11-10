/-
P2.5：v2c の 1KB より長い経路（`hash_long_b`）の ε。NH32×2 と多項式 mod 2⁶¹−1 と multiply-shift の 3 段の合成。

流れ:
  バイト列 ─(Spec/Long)→ ブロックごとのレーン ─(NH32×2)→ (x_j, y_j) ─(60bit limb)→ 係数列
    ─(Horner mod p、最後に L)→ h ┐
    t = Σ y_j mod 2⁶⁴ ───────────┴→ h·2⁶⁴ + t ─(multiply-shift)→ 64bit ─(^ fin_long, fmix64)→ 出力

鍵（独立で一様）: NH の鍵 K（`KeyB`）、評価点 r ∈ ZMod p、乗数 m（`odd128`）、fin_long。

ε の内訳（`long_eps`）:
- 係数列が違う（長さが同じで中身が違う、または定数項 L が違う）：差の多項式の根は 3N 個以下 → 3N/p（`horner_au`）
- 係数列が同じ：長さが同じで全ブロックの NH 出力が同じ。違いのあるブロックで NH32×2 が衝突する確率 2⁻⁶⁴（`nhT_eau`）
- multiply-shift：2⁻⁶³（`ms_au`）
- 仕上げ（^ fin_long、fmix64）は衝突を変えない（`out_eq_iff`）
合計 2⁻⁶⁴ + 3N/p + 2⁻⁶³ ≤ 2⁻⁶³ + (3N+1)/p。N はブロック数 ⌊L/1024⌋ + 1 の大きいほう。
-/
import LeanHash.Spec.Long
import LeanHash.Props.Poly
import LeanHash.Props.ShortPath

namespace LeanHash.Props

open Finset LeanHash.Spec

/-- ブロック j の NH32×2 の出力。 -/
def outL (K : KeyB) (s : Bytes) (j : ℕ) : ZMod ((2 ^ 32) ^ 2) × ZMod ((2 ^ 32) ^ 2) :=
  nhT K (msgL s j)

/-- 出力 (x, y) を v = x + 2⁶⁴·y の 60bit limb 3 つに（Rust の `absorb`）。 -/
def limbs (o : ZMod ((2 ^ 32) ^ 2) × ZMod ((2 ^ 32) ^ 2)) : List (ZMod P61) :=
  let v := o.1.val + 2 ^ 64 * o.2.val
  [((v % 2 ^ 60 : ℕ) : ZMod P61), ((v / 2 ^ 60 % 2 ^ 60 : ℕ) : ZMod P61), ((v / 2 ^ 120 : ℕ) : ZMod P61)]

/-- 全ブロックの出力。 -/
def outs (K : KeyB) (s : Bytes) : List (ZMod ((2 ^ 32) ^ 2) × ZMod ((2 ^ 32) ^ 2)) :=
  (List.range (nBlk s.length)).map (outL K s)

/-- 多項式の係数列（長さの係数を除く）。 -/
def coefs (K : KeyB) (s : Bytes) : List (ZMod P61) := (outs K s).flatMap limbs

/-- 多項式段 h = Horner(r; limb…, L) mod p。 -/
def polyH (K : KeyB) (r : ZMod P61) (s : Bytes) : ZMod P61 :=
  horner r (coefs K s ++ [(s.length : ZMod P61)])

/-- t = Σ y_j mod 2⁶⁴。 -/
def tsum (K : KeyB) (s : Bytes) : ℕ := ((outs K s).map fun o => o.2.val).sum % 2 ^ 64

/-- multiply-shift まで（`ms(m, h·2⁶⁴ + t)`）。 -/
def preL (K : KeyB) (r : ZMod P61) (m : ℕ) (s : Bytes) : ℕ :=
  ms 128 64 m ((polyH K r s).val * 2 ^ 64 + tsum K s)

/-- 出力（v2c の `fmix64(ms(m, (h << 64) | t) ^ fin_long)`）。 -/
def hashL (K : KeyB) (r : ZMod P61) (m : ℕ) (fin : BitVec 64) (s : Bytes) : BitVec 64 :=
  out fin (preL K r m s)

theorem hashL_eq_iff (K : KeyB) (r : ZMod P61) (m : ℕ) (fin : BitVec 64) (s s' : Bytes) :
    hashL K r m fin s = hashL K r m fin s' ↔ preL K r m s = preL K r m s' :=
  out_eq_iff fin (ms_lt _ _) (ms_lt _ _)

/-! ### limb と係数列 -/

theorem length_limbs (o : ZMod ((2 ^ 32) ^ 2) × ZMod ((2 ^ 32) ^ 2)) : (limbs o).length = 3 := rfl

theorem natCast_inj_p61 {a b : ℕ} (ha : a < 2 ^ 60) (hb : b < 2 ^ 60)
    (h : (a : ZMod P61) = (b : ZMod P61)) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (ha.trans_le (by norm_num)),
    Nat.mod_eq_of_lt (hb.trans_le (by norm_num))] at this

theorem limbs_inj {o o' : ZMod ((2 ^ 32) ^ 2) × ZMod ((2 ^ 32) ^ 2)} (h : limbs o = limbs o') :
    o = o' := by
  have hx : o.1.val < 2 ^ 64 := (ZMod.val_lt _).trans_eq (by norm_num)
  have hy : o.2.val < 2 ^ 64 := (ZMod.val_lt _).trans_eq (by norm_num)
  have hx' : o'.1.val < 2 ^ 64 := (ZMod.val_lt _).trans_eq (by norm_num)
  have hy' : o'.2.val < 2 ^ 64 := (ZMod.val_lt _).trans_eq (by norm_num)
  simp only [limbs, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2⟩ := h
  set v := o.1.val + 2 ^ 64 * o.2.val with hv
  set v' := o'.1.val + 2 ^ 64 * o'.2.val with hv'
  have e0 := natCast_inj_p61 (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h0
  have e1 := natCast_inj_p61 (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1
  have e2 := natCast_inj_p61 (Nat.div_lt_of_lt_mul (by omega)) (Nat.div_lt_of_lt_mul (by omega)) h2
  have hvv : v = v' := by
    have d1 := Nat.div_add_mod v (2 ^ 60)
    have d2 := Nat.div_add_mod (v / 2 ^ 60) (2 ^ 60)
    have d1' := Nat.div_add_mod v' (2 ^ 60)
    have d2' := Nat.div_add_mod (v' / 2 ^ 60) (2 ^ 60)
    rw [Nat.div_div_eq_div_mul] at d2 d2'
    rw [show 2 ^ 60 * 2 ^ 60 = 2 ^ 120 by norm_num] at d2 d2'
    rw [← d1, ← d2, ← d1', ← d2', e0, e1, e2]
  exact Prod.ext (ZMod.val_injective _ (by omega)) (ZMod.val_injective _ (by omega))

/-- 長さ 3 の列を返す単射 f の flatMap は単射。 -/
theorem flatMap_limbs_inj {l l' : List (ZMod ((2 ^ 32) ^ 2) × ZMod ((2 ^ 32) ^ 2))}
    (hlen : l.length = l'.length) (h : l.flatMap limbs = l'.flatMap limbs) : l = l' := by
  induction l generalizing l' with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons a l ih =>
    cases l' with
    | nil => simp at hlen
    | cons a' l' =>
      simp only [List.flatMap_cons] at h
      obtain ⟨ha, hl⟩ := List.append_inj h (by rw [length_limbs, length_limbs])
      rw [limbs_inj ha, ih (by simpa using hlen) hl]

theorem length_coefs (K : KeyB) (s : Bytes) : (coefs K s).length = 3 * nBlk s.length := by
  simp only [coefs, outs, List.length_flatMap, List.map_map, Function.comp_def, length_limbs,
    List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
  ring

/-- 係数列が同じ（同じ長さで）なら、すべてのブロックの NH 出力が同じ。 -/
theorem outL_eq_of_coefs {K : KeyB} {s s' : Bytes} (hlen : s.length = s'.length)
    (h : coefs K s = coefs K s') {j : ℕ} (hj : j < nBlk s.length) : outL K s j = outL K s' j := by
  have e := flatMap_limbs_inj (by simp [outs, hlen]) h
  have := congrArg (fun l => l[j]?) e
  simp only [outs, ← hlen, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.some.injEq] at this
  exact this

/-! ### 数え上げ -/

/-- **2 段の数え上げ（鍵が独立）。** 1 段目の鍵 K で事象 E が起きなければ、2 段目で衝突する ρ は c 個以下。 -/
theorem card_two_stage {κ ρ : Type*} [Fintype κ] [Fintype ρ] (E : κ → Prop) [DecidablePred E]
    (C : κ → ρ → Prop) [∀ K, DecidablePred (C K)]
    (c : ℕ) (hE : ∀ K, ¬E K → (univ.filter (C K)).card ≤ c) :
    (univ.filter fun p : κ × ρ => C p.1 p.2).card ≤
      (univ.filter E).card * Fintype.card ρ + Fintype.card κ * c := by
  rw [← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
  have hK : ∀ K, (∑ r, if C K r then 1 else 0) ≤ (if E K then Fintype.card ρ else 0) + c := by
    intro K
    rw [← Finset.card_filter]
    by_cases h : E K
    · simp only [h, ite_true]
      exact (Finset.card_le_univ _).trans (Nat.le_add_right _ _)
    · simp only [h, ite_false, zero_add]
      exact hE K h
  calc _ ≤ ∑ K, ((if E K then Fintype.card ρ else 0) + c) := Finset.sum_le_sum fun K _ => hK K
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

/-- 多項式段：係数列が同じ鍵を除けば、h が衝突する r は 3N 個以下。 -/
theorem card_polyH (s s' : Bytes) (hL : s.length < P61) (hL' : s'.length < P61) :
    (univ.filter fun p : KeyB × ZMod P61 => polyH p.1 p.2 s = polyH p.1 p.2 s').card ≤
      (univ.filter fun K : KeyB => s.length = s'.length ∧ coefs K s = coefs K s').card * P61 +
        Fintype.card KeyB * (3 * max (nBlk s.length) (nBlk s'.length)) := by
  classical
  have h := card_two_stage (fun K : KeyB => s.length = s'.length ∧ coefs K s = coefs K s')
    (fun K r => polyH K r s = polyH K r s') (3 * max (nBlk s.length) (nBlk s'.length)) ?_
  · rwa [ZMod.card] at h
  intro K hK
  refine horner_au (by rw [length_coefs]; omega) (by rw [length_coefs]; omega) ?_
  by_cases hlen : s.length = s'.length
  · refine Or.inl ⟨by rw [length_coefs, length_coefs, hlen], fun e => hK ⟨hlen, ?_⟩⟩
    exact List.append_inj_left e (by rw [length_coefs, length_coefs, hlen])
  · refine Or.inr fun e => hlen ?_
    have := congrArg ZMod.val e
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hL'] at this

set_option linter.constructorNameAsVariable false in
/-- NH 段：違う 2 入力で係数列が同じになる鍵は 2⁻⁶⁴ の割合以下。 -/
theorem card_coefs_eq {s s' : Bytes} (hs : 1024 < s.length) (hne : s ≠ s') :
    (univ.filter fun K : KeyB => s.length = s'.length ∧ coefs K s = coefs K s').card * 2 ^ 64 ≤
      Fintype.card KeyB := by
  classical
  by_cases hlen : s.length = s'.length
  · -- 違いのあるブロック j
    have hj : ∃ j < nBlk s.length, msgL s j ≠ msgL s' j := by
      by_contra hc
      push Not at hc
      exact hne (msgL_inj hlen hs hc)
    obtain ⟨j, hjN, hjne⟩ := hj
    obtain ⟨jj, hjj⟩ := exists_lastDiff _ _ hjne (msgL_isSome hlen (by omega) j)
    have hnh := nhT_eau (msgL s j) (msgL s' j) jj hjj
    have hsub : (univ.filter fun K : KeyB => s.length = s'.length ∧ coefs K s = coefs K s') ⊆
        univ.filter fun K : KeyB => nhT K (msgL s j) = nhT K (msgL s' j) := by
      intro K hK
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK ⊢
      exact outL_eq_of_coefs hlen hK.2 hjN
    calc _ ≤ (univ.filter fun K : KeyB => nhT K (msgL s j) = nhT K (msgL s' j)).card * 2 ^ 64 :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ = (univ.filter fun K : KeyB => nhT K (msgL s j) = nhT K (msgL s' j)).card *
          ((2 : ℕ) ^ 32) ^ 2 := by norm_num
      _ ≤ _ := by rw [card_keys]; exact hnh
  · have : (univ.filter fun K : KeyB => s.length = s'.length ∧ coefs K s = coefs K s') = ∅ :=
      Finset.filter_false_of_mem fun K _ h => hlen h.1
    rw [this, Finset.card_empty, zero_mul]
    exact Nat.zero_le _

theorem polyH_val_lt (K : KeyB) (r : ZMod P61) (s : Bytes) : (polyH K r s).val < 2 ^ 64 :=
  (ZMod.val_lt _).trans (by norm_num)

theorem tsum_lt (K : KeyB) (s : Bytes) : tsum K s < 2 ^ 64 := Nat.mod_lt _ (by norm_num)

/-- 確率の足し算（鍵の総数は抽象的なまま。展開させない）。 -/
theorem long_ratio (Kc Pc A F coll n : ℕ) (hP : 0 < Pc) (hA : A * 2 ^ 64 ≤ Kc)
    (hF : F ≤ A * Pc + Kc * n) (hc : coll ≤ F * 2 ^ 127 + Kc * Pc * 2 ^ 64) :
    (coll : ℚ) / (Kc * Pc * 2 ^ 127) ≤ 1 / 2 ^ 64 + n / Pc + 1 / 2 ^ 63 := by
  rcases Nat.eq_zero_or_pos Kc with hK | hK
  · subst hK; simp only [Nat.cast_zero, zero_mul, div_zero]; positivity
  have h1 : A * Pc * 2 ^ 127 ≤ Kc * Pc * 2 ^ 63 := by
    calc A * Pc * 2 ^ 127 = A * 2 ^ 64 * (Pc * 2 ^ 63) := by ring
      _ ≤ Kc * (Pc * 2 ^ 63) := Nat.mul_le_mul_right _ hA
      _ = _ := by ring
  have h2 : coll ≤ Kc * Pc * 2 ^ 63 + Kc * n * 2 ^ 127 + Kc * Pc * 2 ^ 64 := by
    calc coll ≤ (A * Pc + Kc * n) * 2 ^ 127 + Kc * Pc * 2 ^ 64 :=
          hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hF) _)
      _ = A * Pc * 2 ^ 127 + Kc * n * 2 ^ 127 + Kc * Pc * 2 ^ 64 := by ring
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right h1 _) _
  have hPq : (0 : ℚ) < Pc := by exact_mod_cast hP
  have hKq : (0 : ℚ) < Kc := by exact_mod_cast hK
  rw [div_le_iff₀ (by positivity)]
  have e : ((1 : ℚ) / 2 ^ 64 + n / Pc + 1 / 2 ^ 63) * (Kc * Pc * 2 ^ 127) =
      (Kc * Pc * 2 ^ 63 + Kc * n * 2 ^ 127 + Kc * Pc * 2 ^ 64 : ℕ) := by
    push_cast
    field_simp
    ring
  rw [e]
  exact_mod_cast h2

/-! ### 主定理 -/

set_option linter.constructorNameAsVariable false in
/-- **v2c の長い経路（L > 1024）の ε。** 違う 2 入力（長さ < p）について、
鍵 (K, r, m) が一様なら Pr[衝突] ≤ 2⁻⁶⁴ + 3N/p + 2⁻⁶³（N はブロック数の大きいほう）。
fin_long と fmix64 は `hashL_eq_iff` により衝突を変えない。 -/
theorem long_eps (s s' : Bytes) (hs : 1024 < s.length) (hL : s.length < P61)
    (hL' : s'.length < P61) (hne : s ≠ s') :
    ((((univ : Finset (KeyB × ZMod P61)) ×ˢ odd128).filter fun p =>
        preL p.1.1 p.1.2 p.2 s = preL p.1.1 p.1.2 p.2 s').card : ℚ) /
      (Fintype.card KeyB * P61 * odd128.card) ≤
      1 / 2 ^ 64 + (3 * max (nBlk s.length) (nBlk s'.length) : ℕ) / P61 + 1 / 2 ^ 63 := by
  classical
  set f : KeyB × ZMod P61 → ℕ := fun p => (polyH p.1 p.2 s).val * 2 ^ 64 + tsum p.1 s
  set f' : KeyB × ZMod P61 → ℕ := fun p => (polyH p.1 p.2 s').val * 2 ^ 64 + tsum p.1 s'
  have hflt : ∀ p, f p < 2 ^ 128 := fun p => by
    have := polyH_val_lt p.1 p.2 s; have := tsum_lt p.1 s; simp only [f]; omega
  have hflt' : ∀ p, f' p < 2 ^ 128 := fun p => by
    have := polyH_val_lt p.1 p.2 s'; have := tsum_lt p.1 s'; simp only [f']; omega
  have hc := card_compose odd128 f f' (ms 128 64) (2 ^ 64)
    fun p h => ms_stage (hflt p) (hflt' p) h
  rw [card_odd128, Fintype.card_prod, ZMod.card] at hc
  -- f が衝突すれば h も衝突する
  have hsub : (univ.filter fun p : KeyB × ZMod P61 => f p = f' p) ⊆
      univ.filter fun p : KeyB × ZMod P61 => polyH p.1 p.2 s = polyH p.1 p.2 s' := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, f'] at hp ⊢
    have := tsum_lt p.1 s; have := tsum_lt p.1 s'
    exact ZMod.val_injective _ (by omega)
  rw [card_odd128]
  have hP : (P61 : ℚ) = ((P61 : ℕ) : ℚ) := rfl
  rw [show ((2 : ℕ) ^ 127 : ℕ) = 2 ^ 127 from rfl]
  have := long_ratio (Fintype.card KeyB) P61
    (univ.filter fun K : KeyB => s.length = s'.length ∧ coefs K s = coefs K s').card
    (univ.filter fun p : KeyB × ZMod P61 => polyH p.1 p.2 s = polyH p.1 p.2 s').card
    _ (3 * max (nBlk s.length) (nBlk s'.length)) (by norm_num) (card_coefs_eq hs hne)
    (card_polyH s s' hL hL')
    (hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Finset.card_le_card hsub)) _))
  push_cast at this ⊢
  exact this

/-- 承認済みの目標の形：2⁻⁶⁴ + 3N/p + 2⁻⁶³ ≤ 2⁻⁶³ + (3N+1)/p。 -/
theorem long_eps_le_target (N : ℕ) :
    (1 : ℚ) / 2 ^ 64 + (3 * N : ℕ) / P61 + 1 / 2 ^ 63 ≤ 1 / 2 ^ 63 + (3 * N + 1 : ℕ) / P61 := by
  have h : (1 : ℚ) / 2 ^ 64 ≤ 1 / P61 := by norm_num
  have e : ((3 * N + 1 : ℕ) : ℚ) / P61 = ((3 * N : ℕ) : ℚ) / P61 + 1 / P61 := by
    push_cast; ring
  rw [e]
  linarith

end LeanHash.Props
