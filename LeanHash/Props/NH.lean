/-
P2：NH は (1/W)-AU。長さの等しい異なるメッセージ M ≠ M' について、
一様な鍵 K で NH_K(M) = NH_K(M') となる確率は 1/W 以下（W = 2ʷ なら 2⁻ʷ）。

証明の流れ（詳細は docs/journal/2026-11-08-p2-nh-eau.md）:
1. `inj_second`：1 語目の値が違えば、2 語目の鍵 ↦ 1 組の差 は単射（`NHCore.core` を使う）
2. `pd_inj2` / `pd_inj1`：違う語がどちらでも、その語に対応しない方の鍵について単射
3. `nh_eau`：違う組 i 以外の鍵を固定すると残りの和は一定。S × Fin W → 鍵 の単射を作って数える
-/
import LeanHash.Spec.NH
import LeanHash.Props.NHCore

namespace LeanHash.Props

open LeanHash.Spec Finset

variable {W n : ℕ}

/-- 1 組の差。 -/
def pd (m m' k : Fin W × Fin W) : ZMod (W ^ 2) :=
  (pairVal m k : ZMod (W ^ 2)) - pairVal m' k

/-- (m + k) mod W を整数で書く。 -/
theorem val_add_int (m k : Fin W) : (((m + k : Fin W) : ℕ) : ℤ) = ((m : ℤ) + k) % W := by
  rw [Fin.val_add]; push_cast; rfl

/-- Fin W の値は整数として 0 以上 W 未満。 -/
theorem fin_bound (x : Fin W) : 0 ≤ ((x : ℕ) : ℤ) ∧ ((x : ℕ) : ℤ) < W :=
  ⟨by positivity, by exact_mod_cast x.isLt⟩

/-- 1 語目の値 a ≠ a' なら、2 語目の鍵 k ↦ a·((m₂ + k) mod W) − a'·((m₂' + k) mod W) は単射。 -/
theorem inj_second (a a' : Fin W) (hne : a ≠ a') (m2 m2' : Fin W) :
    Function.Injective fun k : Fin W =>
      ((a : ℕ) * ((m2 + k : Fin W) : ℕ) : ZMod (W ^ 2)) - ((a' : ℕ) * ((m2' + k : Fin W) : ℕ)) := by
  intro k l h
  simp only at h
  have hW : 0 < W := Fin.pos k
  -- 整数に移して W² ∣ 差 を得る
  have h' : ((((a : ℕ) : ℤ) * (((m2 + k : Fin W) : ℕ) : ℤ)
        - ((a' : ℕ) : ℤ) * (((m2' + k : Fin W) : ℕ) : ℤ) : ℤ) : ZMod (W ^ 2)) =
      ((((a : ℕ) : ℤ) * (((m2 + l : Fin W) : ℕ) : ℤ)
        - ((a' : ℕ) : ℤ) * (((m2' + l : Fin W) : ℕ) : ℤ) : ℤ) : ZMod (W ^ 2)) := by
    push_cast; exact h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
  push_cast at h'
  -- d = x(l) − x(k)、d' = x'(l) − x'(k)
  have bxk := fin_bound (m2 + k)
  have bxl := fin_bound (m2 + l)
  have byk := fin_bound (m2' + k)
  have byl := fin_bound (m2' + l)
  set xk := (((m2 + k : Fin W) : ℕ) : ℤ) with hxk
  set xl := (((m2 + l : Fin W) : ℕ) : ℤ) with hxl
  set yk := (((m2' + k : Fin W) : ℕ) : ℤ) with hyk
  set yl := (((m2' + l : Fin W) : ℕ) : ℤ) with hyl
  have hmod : (W : ℤ) ∣ (yl - yk) - (xl - xk) := by
    rw [hxk, hxl, hyk, hyl, val_add_int, val_add_int, val_add_int, val_add_int,
      Int.emod_def, Int.emod_def, Int.emod_def, Int.emod_def]
    exact ⟨((m2 : ℤ) + l) / W - ((m2 : ℤ) + k) / W - ((m2' : ℤ) + l) / W + ((m2' : ℤ) + k) / W,
      by ring⟩
  have hd := core (W : ℤ) (a : ℕ) (a' : ℕ) (xl - xk) (yl - yk)
    (by positivity) (by exact_mod_cast a.isLt) (by positivity) (by exact_mod_cast a'.isLt)
    (by exact_mod_cast fun e => hne (Fin.ext e))
    (by omega)
    (by omega)
    (by omega)
    (by omega)
    hmod
    (by have e : (a : ℤ) * (xl - xk) - (a' : ℤ) * (yl - yk) =
          (a * xl - a' * yl) - (a * xk - a' * yk) := by ring
        rw [e]; exact_mod_cast h')
  have : ((m2 + k : Fin W) : ℕ) = ((m2 + l : Fin W) : ℕ) := by omega
  exact add_left_cancel (Fin.ext this)

/-- 1 語目が違えば、1 語目の鍵を固定したとき 2 語目の鍵 ↦ 1 組の差 は単射。 -/
theorem pd_inj2 {m m' : Fin W × Fin W} (h : m.1 ≠ m'.1) (k1 : Fin W) :
    Function.Injective fun k2 => pd m m' (k1, k2) := by
  have hne : m.1 + k1 ≠ m'.1 + k1 := fun e => h (add_right_cancel e)
  intro x y e
  apply inj_second _ _ hne m.2 m'.2
  simpa [pd, pairVal] using e

theorem pairVal_swap (m k : Fin W × Fin W) : pairVal m k = pairVal m.swap k.swap := by
  simp [pairVal, Nat.mul_comm]

/-- 2 語目が違えば、2 語目の鍵を固定したとき 1 語目の鍵 ↦ 1 組の差 は単射（積の順序を入れ替えて帰着）。 -/
theorem pd_inj1 {m m' : Fin W × Fin W} (h : m.2 ≠ m'.2) (k2 : Fin W) :
    Function.Injective fun k1 => pd m m' (k1, k2) := by
  intro x y e
  apply pd_inj2 (m := m.swap) (m' := m'.swap) h k2
  simpa [pd, pairVal_swap m, pairVal_swap m'] using e

/-- NH の差は各組の差の和。 -/
theorem nh_sub (K M M' : Fin n → Fin W × Fin W) :
    nh K M - nh K M' = ∑ j, pd (M j) (M' j) (K j) := by
  simp [nh, pd, Finset.sum_sub_distrib]

/-- 衝突する 2 つの鍵が組 i 以外で一致すれば、組 i の差も一致する。 -/
theorem pd_eq_of_agree {K K' M M' : Fin n → Fin W × Fin W} (i : Fin n)
    (hK : nh K M = nh K M') (hK' : nh K' M = nh K' M') (hag : ∀ j, j ≠ i → K j = K' j) :
    pd (M i) (M' i) (K i) = pd (M i) (M' i) (K' i) := by
  have e1 := nh_sub K M M'
  have e2 := nh_sub K' M M'
  rw [hK, sub_self, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at e1
  rw [hK', sub_self, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at e2
  have hrest : ∑ j ∈ univ.erase i, pd (M j) (M' j) (K j) =
      ∑ j ∈ univ.erase i, pd (M j) (M' j) (K' j) :=
    Finset.sum_congr rfl fun j hj => by rw [hag j (Finset.ne_of_mem_erase hj)]
  rw [hrest] at e1
  exact add_right_cancel (e1.symm.trans e2)

/-- 数え上げの道具：S × T → α が S 上で単射なら |S|·|T| ≤ |α|。 -/
theorem card_mul_le_of_inj {α T : Type*} [Fintype α] [Fintype T] (S : Finset α)
    (φ : α → T → α) (hinj : ∀ K ∈ S, ∀ K' ∈ S, ∀ t t', φ K t = φ K' t' → K = K' ∧ t = t') :
    S.card * Fintype.card T ≤ Fintype.card α := by
  classical
  rw [← Finset.card_univ (α := T), ← Finset.card_product, ← Finset.card_univ (α := α)]
  refine Finset.card_le_card_of_injOn (fun p => φ p.1 p.2) (fun _ _ => Finset.mem_univ _) ?_
  rintro ⟨K, t⟩ hp ⟨K', t'⟩ hp' e
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
  obtain ⟨h1, h2⟩ := hinj K hp.1 K' hp'.1 t t' e
  simp [h1, h2]

/-- 鍵の総数は W^(2n)。 -/
theorem card_keys : Fintype.card (Fin n → Fin W × Fin W) = W ^ (2 * n) := by
  simp [Fintype.card_prod, pow_mul, sq]

/-- **P2 の主定理：NH は (1/W)-AU。** M ≠ M' なら、衝突する鍵の数 × W ≤ 鍵の総数 W^(2n)。 -/
theorem nh_eau (M M' : Fin n → Fin W × Fin W) (hM : M ≠ M') :
    (univ.filter fun K => nh K M = nh K M').card * W ≤ W ^ (2 * n) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hM
  suffices h : (univ.filter fun K => nh K M = nh K M').card * Fintype.card (Fin W) ≤
      Fintype.card (Fin n → Fin W × Fin W) by
    rwa [Fintype.card_fin, card_keys] at h
  by_cases h1 : (M i).1 ≠ (M' i).1
  · -- 組 i の 2 語目の鍵をずらす
    refine card_mul_le_of_inj _ (fun K t => Function.update K i ((K i).1, (K i).2 + t)) ?_
    intro K hK K' hK' t t' e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK hK'
    have hag : ∀ j, j ≠ i → K j = K' j := fun j hj => by
      simpa [Function.update_of_ne hj] using congrFun e j
    have hi' := congrFun e i
    simp only [Function.update_self, Prod.mk.injEq] at hi'
    have hpd := pd_eq_of_agree i hK hK' hag
    have h2 : (K i).2 = (K' i).2 := by
      apply pd_inj2 h1 (K i).1
      simp only
      conv_rhs => rw [hi'.1]
      exact hpd
    have hKi : K i = K' i := Prod.ext hi'.1 h2
    have hKK : K = K' := funext fun j => by
      by_cases hj : j = i
      · subst hj; exact hKi
      · exact hag j hj
    refine ⟨hKK, ?_⟩
    rw [h2] at hi'
    exact add_left_cancel hi'.2
  · -- 1 語目が同じなら 2 語目が違う。組 i の 1 語目の鍵をずらす
    push Not at h1
    have h2' : (M i).2 ≠ (M' i).2 := fun e => hi (Prod.ext h1 e)
    refine card_mul_le_of_inj _ (fun K t => Function.update K i ((K i).1 + t, (K i).2)) ?_
    intro K hK K' hK' t t' e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK hK'
    have hag : ∀ j, j ≠ i → K j = K' j := fun j hj => by
      simpa [Function.update_of_ne hj] using congrFun e j
    have hi' := congrFun e i
    simp only [Function.update_self, Prod.mk.injEq] at hi'
    have hpd := pd_eq_of_agree i hK hK' hag
    have h1' : (K i).1 = (K' i).1 := by
      apply pd_inj1 h2' (K i).2
      simp only
      conv_rhs => rw [hi'.2]
      exact hpd
    have hKi : K i = K' i := Prod.ext h1' hi'.2
    have hKK : K = K' := funext fun j => by
      by_cases hj : j = i
      · subst hj; exact hKi
      · exact hag j hj
    refine ⟨hKK, ?_⟩
    rw [h1'] at hi'
    exact add_left_cancel hi'.1

/-- 確率の形：Pr_K[NH_K(M) = NH_K(M')] ≤ 1/W。 -/
theorem nh_eau_prob [NeZero W] (M M' : Fin n → Fin W × Fin W) (hM : M ≠ M') :
    ((univ.filter fun K => nh K M = nh K M').card : ℚ) /
      Fintype.card (Fin n → Fin W × Fin W) ≤ 1 / W := by
  have hW : (0 : ℚ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hc := nh_eau M M' hM
  rw [card_keys, div_le_div_iff₀ (by push_cast; exact pow_pos hW _) hW]
  exact_mod_cast (by linarith : _)

/-- w ビット語（W = 2ʷ）では ε = 2⁻ʷ。 -/
theorem nh_eau_pow2 (w : ℕ) (M M' : Fin n → Fin (2 ^ w) × Fin (2 ^ w)) (hM : M ≠ M') :
    ((univ.filter fun K => nh K M = nh K M').card : ℚ) /
      Fintype.card (Fin n → Fin (2 ^ w) × Fin (2 ^ w)) ≤ 1 / 2 ^ w := by
  have := nh_eau_prob M M' hM
  push_cast at this
  exact this

end LeanHash.Props
