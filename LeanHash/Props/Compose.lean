/-
P2 残り 3：合成則。

- `card_compose`：鍵 (K, a) が独立なとき、Pr[g_a(f_K(x)) = g_a(f_K(y))] ≤ Pr[f_K(x) = f_K(y)] + max_{u≠v} Pr[g_a(u) = g_a(v)]
- `out_eq_iff`：仕上げ fmix64(· ^ fin) は fin ごとに単射なので、衝突確率を変えない
- `card_xor_collide`：経路ごとに独立な fin を使えば、経路をまたぐ 2 入力の衝突確率はちょうど 1/2⁶⁴
-/
import Mathlib
import LeanHash.Spec.Fmix

namespace LeanHash.Props

open Finset LeanHash.Spec

/-- **合成の数え上げ。** 2 段目 g が「違う入力で衝突する a は c 個以下」なら、
(K, a) で衝突する組の数 ≤ （1 段目が衝突する K の数）·|A| + |K 全体|·c。 -/
theorem card_compose {κ : Type*} [Fintype κ] (A : Finset ℕ) (f f' : κ → ℕ) (g : ℕ → ℕ → ℕ)
    (c : ℕ) (hg : ∀ K, f K ≠ f' K → (A.filter fun a => g a (f K) = g a (f' K)).card ≤ c) :
    ((univ ×ˢ A).filter fun p : κ × ℕ => g p.2 (f p.1) = g p.2 (f' p.1)).card ≤
      (univ.filter fun K => f K = f' K).card * A.card + Fintype.card κ * c := by
  classical
  rw [Finset.card_filter, Finset.sum_product]
  have hK : ∀ K, (∑ a ∈ A, if g a (f K) = g a (f' K) then 1 else 0) ≤
      (if f K = f' K then A.card else 0) + c := fun K => by
    rw [← Finset.card_filter]
    by_cases h : f K = f' K
    · simp only [h, ite_true]
      exact (Finset.card_filter_le _ _).trans (Nat.le_add_right _ _)
    · simp only [h, ite_false, zero_add]
      exact hg K h
  calc _ ≤ ∑ K, ((if f K = f' K then A.card else 0) + c) := Finset.sum_le_sum fun K _ => hK K
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

/-- 仕上げ：64bit に入れて fin と XOR し、fmix64。 -/
def out (fin : BitVec 64) (pre : ℕ) : BitVec 64 := fmix64 (BitVec.ofNat 64 pre ^^^ fin)

/-- **仕上げは衝突を増やさない。** 2⁶⁴ 未満の値なら、どの fin でも 出力が同じ ⇔ 入力が同じ。 -/
theorem out_eq_iff (fin : BitVec 64) {p q : ℕ} (hp : p < 2 ^ 64) (hq : q < 2 ^ 64) :
    out fin p = out fin q ↔ p = q := by
  constructor
  · intro h
    have h1 := BitVec.xor_left_inj fin |>.mp (fmix64_injective h)
    have h2 := congrArg BitVec.toNat h1
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at h2
    exact h2
  · rintro rfl; rfl

theorem card_bitvec64 : Fintype.card (BitVec 64) = 2 ^ 64 := by
  rw [Fintype.card_congr (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ :
    BitVec 64 ≃ Fin (2 ^ 64)), Fintype.card_fin]

/-- **経路ごとに独立な fin を使ったときの経路またぎ。** どんな u, v でも、
u ^ fin₁ = v ^ fin₂ となる (fin₁, fin₂) はちょうど 2⁶⁴ 組（全 2¹²⁸ 組のうち）。 -/
theorem card_xor_collide (u v : BitVec 64) :
    (univ.filter fun p : BitVec 64 × BitVec 64 => u ^^^ p.1 = v ^^^ p.2).card = 2 ^ 64 := by
  classical
  have e : (univ.filter fun p : BitVec 64 × BitVec 64 => u ^^^ p.1 = v ^^^ p.2) =
      univ.image fun a : BitVec 64 => (a, v ^^^ u ^^^ a) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro h
      refine ⟨a, rfl, ?_⟩
      rw [BitVec.xor_assoc, h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rintro ⟨a', rfl, rfl⟩
      rw [← BitVec.xor_assoc, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  rw [e, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), Finset.card_univ,
    card_bitvec64]

/-- 経路ごとの fin が独立なら、出力（fmix64 後）の衝突も 2⁶⁴ 組。 -/
theorem card_out_collide (p q : ℕ) :
    (univ.filter fun f : BitVec 64 × BitVec 64 => out f.1 p = out f.2 q).card = 2 ^ 64 := by
  have e : (univ.filter fun f : BitVec 64 × BitVec 64 => out f.1 p = out f.2 q) =
      univ.filter fun f : BitVec 64 × BitVec 64 =>
        BitVec.ofNat 64 p ^^^ f.1 = BitVec.ofNat 64 q ^^^ f.2 :=
    Finset.filter_congr fun f _ => ⟨fun h => fmix64_injective h, fun h => by simp [out, h]⟩
  rw [e, card_xor_collide]

end LeanHash.Props
