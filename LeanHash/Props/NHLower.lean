/-
P2：NH の上界 1/W は改善できない（下限）。

`nh_eau` は「M ≠ M' なら衝突確率 ≤ 1/W」。ここでは等号になる組を作る。

- M = 全部 0、M' = 組 i の 1 語目だけ 1（ほかは 0）
- 組 i 以外は同じなので、差は組 i の分だけ: k₁·k₂ − ((1 + k₁) mod W)·k₂
- k₂ = 0 なら右の因数が 0 になり、1 語目の違いが消えて衝突する
- k₂ ≠ 0 なら、両方の積は W² 未満なので自然数として等しいことになり、k₁ = (1 + k₁) mod W。W > 1 では起こらない
- よって衝突 ⇔ (K i).2 = 0。そういう鍵はちょうど W^(2n) / W 個

詳細は docs/journal/2026-11-09-p2-nh-lower.md
-/
import LeanHash.Props.NH

namespace LeanHash.Props

open LeanHash.Spec Finset

variable {W n : ℕ}

/-- 1 語目だけ 0 と 1 で違う組の差は、2 語目の鍵が 0 のときだけ 0。 -/
theorem pd_zero_one_eq_zero_iff [NeZero W] (hW : 1 < W) (k : Fin W × Fin W) :
    pd ((0 : Fin W), (0 : Fin W)) (1, 0) k = 0 ↔ k.2 = 0 := by
  have hlt : ∀ x y : Fin W, (x : ℕ) * y < W ^ 2 := fun x y => by
    rw [sq]; exact Nat.mul_lt_mul'' x.isLt y.isLt
  simp only [pd, pairVal, zero_add, sub_eq_zero]
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt _ _), Nat.mod_eq_of_lt (hlt _ _)]
  constructor
  · intro h
    by_contra hy
    have hy' : ((k.2 : Fin W) : ℕ) ≠ 0 := fun e => hy (Fin.ext (by simpa using e))
    have hx := (Nat.mul_left_inj hy').mp h
    have h1 : (1 : Fin W) = 0 := by
      have : k.1 = 1 + k.1 := Fin.ext hx
      simpa using (add_eq_right.mp this.symm)
    have : ((1 : Fin W) : ℕ) = 1 := by simp [Nat.mod_eq_of_lt hW]
    rw [h1] at this
    simp at this
  · intro h
    simp [h]

/-- 全部 0 のメッセージ。 -/
def zeroMsg [NeZero W] : Fin n → Fin W × Fin W := fun _ => (0, 0)

/-- 組 i の 1 語目だけ 1 にしたメッセージ。 -/
def oneMsg [NeZero W] (i : Fin n) : Fin n → Fin W × Fin W := Function.update zeroMsg i (1, 0)

theorem zeroMsg_ne_oneMsg [NeZero W] (hW : 1 < W) (i : Fin n) :
    (zeroMsg : Fin n → Fin W × Fin W) ≠ oneMsg i := by
  intro e
  have := congrArg Prod.fst (congrFun e i)
  simp only [oneMsg, Function.update_self, zeroMsg] at this
  have h1 : ((1 : Fin W) : ℕ) = 1 := by simp [Nat.mod_eq_of_lt hW]
  rw [← this] at h1
  simp at h1

/-- この 2 つのメッセージが衝突する ⇔ 組 i の 2 語目の鍵が 0。 -/
theorem nh_collide_iff [NeZero W] (hW : 1 < W) (i : Fin n) (K : Fin n → Fin W × Fin W) :
    nh K zeroMsg = nh K (oneMsg i) ↔ (K i).2 = 0 := by
  rw [← sub_eq_zero, nh_sub, Finset.sum_eq_single i]
  · simpa [oneMsg, zeroMsg] using pd_zero_one_eq_zero_iff hW (K i)
  · intro j _ hj
    simp [oneMsg, Function.update_of_ne hj, pd]
  · simp

/-- 組 i の 2 語目の鍵が 0 の鍵は、ちょうど全体の 1/W。 -/
theorem card_snd_zero [NeZero W] (i : Fin n) :
    (univ.filter fun K : Fin n → Fin W × Fin W => (K i).2 = 0).card * W = W ^ (2 * n) := by
  classical
  apply le_antisymm
  · -- 上から：2 語目の鍵をずらす写像が単射
    have h := card_mul_le_of_inj (univ.filter fun K : Fin n → Fin W × Fin W => (K i).2 = 0)
      (fun K t => Function.update K i ((K i).1, (K i).2 + t)) ?_
    · rwa [Fintype.card_fin, card_keys] at h
    intro K hK K' hK' t t' e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK hK'
    have hag : ∀ j, j ≠ i → K j = K' j := fun j hj => by
      simpa [Function.update_of_ne hj] using congrFun e j
    have hi' := congrFun e i
    simp only [Function.update_self, Prod.mk.injEq, hK, hK', zero_add] at hi'
    refine ⟨funext fun j => ?_, hi'.2⟩
    by_cases hj : j = i
    · subst hj; exact Prod.ext hi'.1 (hK.trans hK'.symm)
    · exact hag j hj
  · -- 下から：K ↦ (組 i の 2 語目を 0 にした鍵, 元の 2 語目) が単射
    have h := Finset.card_le_card_of_injOn (s := (univ : Finset (Fin n → Fin W × Fin W)))
      (t := (univ.filter fun K : Fin n → Fin W × Fin W => (K i).2 = 0) ×ˢ (univ : Finset (Fin W)))
      (fun K => (Function.update K i ((K i).1, 0), (K i).2)) (fun K _ => by simp) ?_
    · rwa [Finset.card_univ, card_keys, Finset.card_product, Finset.card_univ,
        Fintype.card_fin] at h
    intro K _ K' _ e
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    funext j
    by_cases hj : j = i
    · subst hj
      have := congrArg Prod.fst (congrFun e1 j)
      simp only [Function.update_self] at this
      exact Prod.ext this e2
    · simpa [Function.update_of_ne hj] using congrFun e1 j

/-- **下限：NH の上界 1/W はちょうど達成される。** W > 1 で組が 1 つ以上あれば、
衝突する鍵の数 × W = 鍵の総数 W^(2n) となる異なる 2 つのメッセージがある。 -/
theorem nh_eau_tight [NeZero W] (hW : 1 < W) (i : Fin n) :
    ∃ M M' : Fin n → Fin W × Fin W, M ≠ M' ∧
      (univ.filter fun K => nh K M = nh K M').card * W = W ^ (2 * n) := by
  refine ⟨zeroMsg, oneMsg i, zeroMsg_ne_oneMsg hW i, ?_⟩
  rw [Finset.filter_congr fun K _ => nh_collide_iff hW i K]
  exact card_snd_zero i

/-- 確率の形：ε = 1/W が NH の正確な値（上界と、それを達成する組）。 -/
theorem nh_eps_exact [NeZero W] (hW : 1 < W) (i : Fin n) :
    (∀ M M' : Fin n → Fin W × Fin W, M ≠ M' →
      ((univ.filter fun K => nh K M = nh K M').card : ℚ) /
        Fintype.card (Fin n → Fin W × Fin W) ≤ 1 / W) ∧
    (∃ M M' : Fin n → Fin W × Fin W, M ≠ M' ∧
      ((univ.filter fun K => nh K M = nh K M').card : ℚ) /
        Fintype.card (Fin n → Fin W × Fin W) = 1 / W) := by
  refine ⟨fun M M' hM => nh_eau_prob M M' hM, ?_⟩
  obtain ⟨M, M', hM, hc⟩ := nh_eau_tight hW i
  refine ⟨M, M', hM, ?_⟩
  have hW0 : (0 : ℚ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  rw [card_keys, div_eq_div_iff (by positivity) hW0.ne']
  exact_mod_cast (by rw [hc]; ring : _ * W = 1 * W ^ (2 * n))

/-- w ビット語（W = 2ʷ、w ≥ 1）では ε = 2⁻ʷ がちょうどの値。 -/
theorem nh_eps_exact_pow2 (w : ℕ) (hw : 0 < w) (i : Fin n) :
    ∃ M M' : Fin n → Fin (2 ^ w) × Fin (2 ^ w), M ≠ M' ∧
      ((univ.filter fun K => nh K M = nh K M').card : ℚ) /
        Fintype.card (Fin n → Fin (2 ^ w) × Fin (2 ^ w)) = 1 / 2 ^ w := by
  have := (nh_eps_exact (Nat.one_lt_two_pow hw.ne') i).2
  push_cast at this
  exact this

end LeanHash.Props
