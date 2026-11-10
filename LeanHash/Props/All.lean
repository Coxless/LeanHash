/-
P2.5 のまとめ：v2c（経路ごとの fin）の全長での ε。

鍵は Rust の `v2::Keys` と同じ形で、すべて独立で一様:
- `Words`：NH の鍵 u64 × 130 語（≤ 32 バイトは `eA`、それ以外は `eB` で読む）
- m：2¹²⁸ 未満の奇数（multiply-shift。全経路で共通）
- `Fins`：(fin, fin_mid)。1KB 以下の 2 経路の仕上げ
- r ∈ ZMod p（p = 2⁶¹ − 1）：多項式の評価点（長い経路だけ）
- fin_long：長い経路の仕上げ

場合分け:
- 両方 1KB 以下：r と fin_long は関係しない → `le1K_eps`（2⁻⁶²）
- 両方 1KB より長い：(fin, fin_mid) は関係しない → `long_eps`（2⁻⁶⁴ + 3N/p + 2⁻⁶³）
- 片方だけ長い：ほかの鍵をどう固定しても、衝突する fin_long は 1 個以下 → 2⁻⁶⁴
どれも 2⁻⁶³ + (3N+1)/p 以下（N はブロック数 ⌊L/1024⌋ + 1 の大きいほう）。
-/
import LeanHash.Props.Le1K
import LeanHash.Props.Long

namespace LeanHash.Props

open Finset LeanHash.Spec

/-- v2c の全体（`hash_c`）。 -/
def hashV2c (w : Words) (m : ℕ) (F : Fins) (r : ZMod P61) (fl : BitVec 64) (s : Bytes) :
    BitVec 64 :=
  if s.length ≤ 1024 then hash1K w m F s else hashL (eB w) r m fl s

/-- 鍵 (((w, m), (fin, fin_mid)), r), fin_long の全体。 -/
abbrev Keys := (((Words × ℕ) × Fins) × ZMod P61) × BitVec 64

def keySet : Finset Keys := (((univ ×ˢ odd128) ×ˢ univ) ×ˢ univ) ×ˢ univ

/-- 主定理の分母は鍵の総数。 -/
theorem card_keySet :
    keySet.card = Fintype.card Words * odd128.card * Fintype.card Fins * P61 * 2 ^ 64 := by
  rw [keySet, Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_product,
    Finset.card_univ, Finset.card_univ, Finset.card_univ, Finset.card_univ, ZMod.card, card_bitvec64]

/-! ### 数え上げの道具 -/

theorem card_filter_fst {α β : Type*} (S : Finset α) (T : Finset β) (Q : α → Prop)
    [DecidablePred Q] : ((S ×ˢ T).filter fun p => Q p.1).card = (S.filter Q).card * T.card := by
  rw [Finset.filter_product_left, Finset.card_product]

/-- 各 x で条件をみたす y が 1 個以下なら、全体で |S| 個以下。 -/
theorem card_filter_le_one {α β : Type*} [Fintype β] (S : Finset α) (P : α → β → Prop)
    [∀ x, DecidablePred (P x)] (h : ∀ x ∈ S, (univ.filter (P x)).card ≤ 1) :
    ((S ×ˢ (univ : Finset β)).filter fun p => P p.1 p.2).card ≤ S.card := by
  rw [Finset.card_filter, Finset.sum_product]
  calc _ = ∑ x ∈ S, (univ.filter (P x)).card :=
        Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm
    _ ≤ ∑ _x ∈ S, 1 := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- 仕上げの fin が 1 つだけ独立なら、出力が一致する fin は 1 個以下。 -/
theorem card_out_fin_le_one (u : BitVec 64) (b : ℕ) :
    (univ.filter fun fl : BitVec 64 => u = out fl b).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro f₁ h₁ f₂ h₂
  have e₁ := (Finset.mem_filter.mp h₁).2
  have e₂ := (Finset.mem_filter.mp h₂).2
  have := fmix64_injective (e₁.symm.trans e₂)
  exact (BitVec.xor_right_inj _).mp this

set_option linter.constructorNameAsVariable false in
/-- 長い経路の場合：鍵の並べ方を (((K, r), m), (F, fin_long)) に変えて数える。 -/
theorem card_regroup (Q : KeyB → ZMod P61 → ℕ → Prop) [∀ K r, DecidablePred (Q K r)]
    [DecidablePred fun p : Keys => Q (eB p.1.1.1.1) p.1.2 p.1.1.1.2]
    [DecidablePred fun p : (KeyB × ZMod P61) × ℕ => Q p.1.1 p.1.2 p.2] :
    (keySet.filter fun p : Keys => Q (eB p.1.1.1.1) p.1.2 p.1.1.1.2).card =
      (((univ : Finset (KeyB × ZMod P61)) ×ˢ odd128).filter fun p => Q p.1.1 p.1.2 p.2).card *
        (Fintype.card Fins * 2 ^ 64) := by
  rw [← card_bitvec64, ← Fintype.card_prod, ← Finset.card_univ,
    ← card_filter_fst _ _ fun p : (KeyB × ZMod P61) × ℕ => Q p.1.1 p.1.2 p.2]
  refine Finset.card_nbij' (fun p => (((eB p.1.1.1.1, p.1.2), p.1.1.1.2), (p.1.1.2, p.2)))
    (fun p => ((((eB.symm p.1.1.1, p.1.2), p.2.1), p.1.1.2), p.2.2)) ?_ ?_ ?_ ?_
  · rintro ⟨⟨⟨⟨w, m⟩, F⟩, r⟩, fl⟩ hp
    simp only [keySet, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product,
      Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hp
  · rintro ⟨⟨⟨K, r⟩, m⟩, F, fl⟩ hp
    simp only [keySet, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product,
      Finset.mem_univ, true_and, and_true, Equiv.apply_symm_apply] at hp ⊢
    exact hp
  · rintro ⟨⟨⟨⟨w, m⟩, F⟩, r⟩, fl⟩ _; simp only [Equiv.symm_apply_apply]
  · rintro ⟨⟨⟨K, r⟩, m⟩, F, fl⟩ _; simp only [Equiv.apply_symm_apply]

/-- 2⁻⁶² と 2⁻⁶⁴ は目標以下（N によらない）。 -/
theorem target_ge (N : ℕ) : (1 : ℚ) / 2 ^ 62 ≤ 1 / 2 ^ 63 + (3 * N + 1 : ℕ) / P61 := by
  have h1 : (1 : ℚ) / 2 ^ 63 ≤ 1 / P61 := by norm_num
  have h2 : (1 : ℚ) / P61 ≤ (3 * N + 1 : ℕ) / P61 :=
    div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_add_left 1 (3 * N)) (by positivity)
  have e : (1 : ℚ) / 2 ^ 62 = 1 / 2 ^ 63 + 1 / 2 ^ 63 := by norm_num
  linarith

/-- 約分（鍵の数は変数のまま。展開させない）。 -/
theorem ratio_short (c W O F P T : ℚ) (hW : W ≠ 0) (hO : O ≠ 0) (hF : F ≠ 0) (hP : P ≠ 0)
    (hT : T ≠ 0) : c * P * T / (W * O * F * P * T) = c / (W * O * F) := by
  rw [div_eq_div_iff (by positivity) (by positivity)]; ring

theorem ratio_long (c K O F P T : ℚ) (hK : K ≠ 0) (hO : O ≠ 0) (hF : F ≠ 0) (hP : P ≠ 0)
    (hT : T ≠ 0) : c * (F * T) / (K * O * F * P * T) = c / (K * P * O) := by
  rw [div_eq_div_iff (by positivity) (by positivity)]; ring

/-! ### 主定理 -/

set_option linter.constructorNameAsVariable false in
/-- **v2c の全長での ε。** 違う 2 入力（長さ < p = 2⁶¹ − 1）について、鍵がすべて独立で一様なら
Pr[衝突] ≤ 2⁻⁶³ + (3N+1)/p（N = max(⌊L/1024⌋ + 1, ⌊L'/1024⌋ + 1)）。 -/
theorem v2c_eps (s s' : Bytes) (hL : s.length < P61) (hL' : s'.length < P61) (hne : s ≠ s') :
    ((keySet.filter fun p : Keys =>
        hashV2c p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 s =
          hashV2c p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 s').card : ℚ) /
      (Fintype.card Words * odd128.card * Fintype.card Fins * P61 * 2 ^ 64) ≤
      1 / 2 ^ 63 + (3 * max (nBlk s.length) (nBlk s'.length) + 1 : ℕ) / P61 := by
  classical
  set N := max (nBlk s.length) (nBlk s'.length)
  have hW : (0 : ℚ) < Fintype.card Words := Nat.cast_pos.mpr Fintype.card_pos
  have hO : (0 : ℚ) < odd128.card := Nat.cast_pos.mpr (by rw [card_odd128]; positivity)
  have hF : (0 : ℚ) < Fintype.card Fins := Nat.cast_pos.mpr Fintype.card_pos
  have hP : (0 : ℚ) < P61 := by norm_num
  -- 片方だけ長い場合：fin_long ごとに 1 個以下
  have cross : ∀ (P : (((Words × ℕ) × Fins) × ZMod P61) → BitVec 64 → Prop)
      [∀ x, DecidablePred (P x)], (∀ x, (univ.filter (P x)).card ≤ 1) →
      ((keySet.filter fun p => P p.1 p.2).card : ℚ) /
        (Fintype.card Words * odd128.card * Fintype.card Fins * P61 * 2 ^ 64) ≤
        1 / 2 ^ 63 + (3 * N + 1 : ℕ) / P61 := by
    intro P _ hP1
    have h := card_filter_le_one (((univ ×ˢ odd128) ×ˢ univ) ×ˢ univ) P fun x _ => hP1 x
    unfold keySet
    rw [Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_univ,
      Finset.card_univ, Finset.card_univ, ZMod.card] at h
    refine le_trans ?_ (le_trans (by norm_num : (1 : ℚ) / 2 ^ 64 ≤ 1 / 2 ^ 62) (target_ge N))
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc ((keySet.filter fun p => P p.1 p.2).card : ℚ) * 2 ^ 64 ≤
          ((Fintype.card Words * odd128.card * Fintype.card Fins * P61 : ℕ) : ℚ) * 2 ^ 64 := by
          gcongr; exact_mod_cast h
      _ = _ := by rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
  by_cases ha : s.length ≤ 1024 <;> by_cases hb : s'.length ≤ 1024
  · -- 両方 1KB 以下
    have e : (keySet.filter fun p : Keys =>
        hashV2c p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 s =
          hashV2c p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 s') =
        ((((univ ×ˢ odd128) ×ˢ (univ : Finset Fins)).filter fun x : (Words × ℕ) × Fins =>
          hash1K x.1.1 x.1.2 x.2 s = hash1K x.1.1 x.1.2 x.2 s') ×ˢ (univ : Finset (ZMod P61))) ×ˢ
          (univ : Finset (BitVec 64)) := by
      ext ⟨⟨⟨⟨w, m⟩, F⟩, r⟩, fl⟩
      simp only [keySet, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
        hashV2c, ha, hb, ↓reduceIte]
    rw [e, Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
      card_bitvec64, ZMod.card]
    have h1 := le1K_eps s s' ha hb hne
    refine le_trans ?_ (h1.trans (target_ge N))
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact le_of_eq (ratio_short _ _ _ _ _ _ hW.ne' hO.ne' hF.ne' hP.ne' (by norm_num))
  · -- s は 1KB 以下、s' は長い
    refine cross (fun x fl => hashV2c x.1.1.1 x.1.1.2 x.1.2 x.2 fl s =
      hashV2c x.1.1.1 x.1.1.2 x.1.2 x.2 fl s') fun x => ?_
    simp only [hashV2c, ha, hb, ↓reduceIte, hashL]
    exact card_out_fin_le_one _ _
  · -- s は長い、s' は 1KB 以下
    refine cross (fun x fl => hashV2c x.1.1.1 x.1.1.2 x.1.2 x.2 fl s =
      hashV2c x.1.1.1 x.1.1.2 x.1.2 x.2 fl s') fun x => ?_
    simp only [hashV2c, ha, hb, ↓reduceIte, hashL]
    simp only [eq_comm (a := out _ _)]
    exact card_out_fin_le_one _ _
  · -- 両方 長い
    have e : (keySet.filter fun p : Keys =>
        hashV2c p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 s =
          hashV2c p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 s') =
        keySet.filter fun p : Keys => (fun K r m => preL K r m s = preL K r m s')
          (eB p.1.1.1.1) p.1.2 p.1.1.1.2 :=
      Finset.filter_congr fun p _ => by
        simp only [hashV2c, ha, hb, ↓reduceIte]; exact hashL_eq_iff _ _ _ _ _ _
    rw [e, card_regroup (fun K r m => preL K r m s = preL K r m s')]
    have h1 := long_eps s s' (by omega) hL hL' hne
    refine le_trans ?_ (h1.trans (long_eps_le_target N))
    rw [Fintype.card_congr eB, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [Fintype.card_congr eB] at hW
    exact le_of_eq (ratio_long _ _ _ _ _ _ hW.ne' hO.ne' hF.ne' hP.ne' (by norm_num))

end LeanHash.Props
