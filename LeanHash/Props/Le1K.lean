/-
P2 のまとめ（経路ごとの fin を入れた v2c）：1KB 以下の違う 2 入力の衝突確率 ≤ 2⁻⁶²。

鍵は Rust の `v2::Keys` と同じ形で、すべて独立で一様:
- `Words`：NH の鍵 u64 × 130 語。経路 A は語 2i, 2i+1 を組 i として（`eA`）、
  経路 B は語 i の下位・上位 32bit をレーン i として（`eB`）読む。どちらも全単射なので一様性はそのまま移る
- m：2¹²⁸ 未満の奇数
- `Fins`：(fin, fin_mid)。経路 A（≤ 32 バイト）は fin、経路 B（33〜1024 バイト）は fin_mid

場合分け:
- 同じ経路：fin は衝突に関係しない（`hashA_eq_iff`）ので `pathA_eps` / `pathB_eps` に帰着 → 2⁻⁶⁴ + 2⁻⁶³
- 経路が違う：(K, m) をどう固定しても、衝突する (fin, fin_mid) はちょうど 2⁶⁴ 組（`card_out_collide`）→ 2⁻⁶⁴
-/
import LeanHash.Props.ShortPath

namespace LeanHash.Props

open Finset LeanHash.Spec

/-- NH の鍵：u64 × 130 語（Rust の `Keys::nh`）。 -/
abbrev Words := Fin 130 → Fin (2 ^ 64)

/-- 仕上げの XOR 定数（fin, fin_mid）。 -/
abbrev Fins := BitVec 64 × BitVec 64

/-! ### 鍵の読み方（全単射） -/

/-- 経路 A：語 2i, 2i+1 を組 i に。 -/
def viewA (w : Words) : KeyA := fun i => (w ⟨2 * i.val, by omega⟩, w ⟨2 * i.val + 1, by omega⟩)

def unA (K : KeyA) : Words := fun j =>
  if j.val % 2 = 0 then (K ⟨j.val / 2, by omega⟩).1 else (K ⟨j.val / 2, by omega⟩).2

/-- 経路 B：語 i の下位 32bit と上位 32bit をレーン i に。 -/
def viewB (w : Words) : KeyB := fun i => (wd 32 (w i).val, wd 32 ((w i).val / 2 ^ 32))

def unB (K : KeyB) : Words := fun i =>
  ⟨(K i).1.val + 2 ^ 32 * (K i).2.val, by have := (K i).1.isLt; have := (K i).2.isLt; omega⟩

def eA : Words ≃ KeyA where
  toFun := viewA
  invFun := unA
  left_inv w := by
    funext j
    simp only [unA, viewA]
    split_ifs with h
    · congr 1; exact Fin.ext (by dsimp only; omega)
    · congr 1; exact Fin.ext (by dsimp only; omega)
  right_inv K := by
    funext i
    simp only [unA, viewA, show 2 * i.val % 2 = 0 by omega, show (2 * i.val + 1) % 2 ≠ 0 by omega,
      ↓reduceIte]
    have e1 : (⟨2 * i.val / 2, by omega⟩ : Fin 65) = i := Fin.ext (by dsimp only; omega)
    have e2 : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin 65) = i := Fin.ext (by dsimp only; omega)
    rw [e1, e2]

def eB : Words ≃ KeyB where
  toFun := viewB
  invFun := unB
  left_inv w := by
    funext i
    have := (w i).isLt
    apply Fin.ext
    simp only [unB, viewB, wd]
    omega
  right_inv K := by
    funext i
    have := (K i).1.isLt
    have := (K i).2.isLt
    apply Prod.ext <;> apply Fin.ext <;> simp only [unB, viewB, wd] <;> omega

/-! ### 1KB 以下の全体の関数 -/

/-- v2c の 1KB 以下（`hash_c` の L ≤ 1024）。 -/
def hash1K (w : Words) (m : ℕ) (f : Fins) (s : Bytes) : BitVec 64 :=
  if s.length ≤ 32 then hashA (eA w) m f.1 s else hashB (eB w) m f.2 s

/-! ### 数え上げの道具 -/

/-- 条件が f によらなければ、f の数だけ倍になる。 -/
theorem card_prod_const {α : Type*} (S : Finset α) (P : α → Fins → Prop) [DecidablePred fun p : α × Fins => P p.1 p.2]
    (Q : α → Prop) [DecidablePred Q] (h : ∀ x ∈ S, ∀ f, P x f ↔ Q x) :
    ((S ×ˢ (univ : Finset Fins)).filter fun p => P p.1 p.2).card =
      (S.filter Q).card * Fintype.card Fins := by
  rw [← Finset.card_univ (α := Fins), ← Finset.card_product]
  congr 1
  ext ⟨x, f⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨hx, hp⟩; exact ⟨hx, (h x hx f).mp hp⟩
  · rintro ⟨hx, hq⟩; exact ⟨hx, (h x hx f).mpr hq⟩

/-- どの x でも条件をみたす f が c 個なら、全体で |S|·c 個。 -/
theorem card_prod_each {α : Type*} (S : Finset α) (P : α → Fins → Prop)
    [∀ x, DecidablePred (P x)] (c : ℕ) (h : ∀ x ∈ S, (univ.filter (P x)).card = c) :
    ((S ×ˢ (univ : Finset Fins)).filter fun p => P p.1 p.2).card = S.card * c := by
  rw [Finset.card_filter, Finset.sum_product]
  calc _ = ∑ x ∈ S, (univ.filter (P x)).card :=
        Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm
    _ = _ := by rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul]

set_option linter.constructorNameAsVariable false in
/-- 鍵の読み方を全単射で変えても、衝突する (鍵, m) の数は同じ。 -/
theorem card_equiv_keys {β : Type*} [Fintype β] (e : Words ≃ β) (g : β → ℕ → Prop)
    [DecidablePred fun p : Words × ℕ => g (e p.1) p.2] [DecidablePred fun p : β × ℕ => g p.1 p.2] :
    ((univ ×ˢ odd128).filter fun p : Words × ℕ => g (e p.1) p.2).card =
      ((univ ×ˢ odd128).filter fun p : β × ℕ => g p.1 p.2).card := by
  refine Finset.card_nbij' (fun p => (e p.1, p.2)) (fun p => (e.symm p.1, p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨K, m⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_univ,
      true_and] at hp ⊢
    exact hp
  · rintro ⟨K, m⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_univ,
      true_and, Equiv.apply_symm_apply] at hp ⊢
    exact hp
  · rintro ⟨K, m⟩ _; simp only [Equiv.symm_apply_apply]
  · rintro ⟨K, m⟩ _; simp only [Equiv.apply_symm_apply]

theorem card_fins : Fintype.card Fins = 2 ^ 128 := by
  rw [Fintype.card_prod, card_bitvec64]; norm_num

/-- 同じ経路の場合：f の分を約分する。 -/
theorem ratio_cancel (c W O F : ℚ) (hF : F ≠ 0) : c * F / (W * O * F) = c / (W * O) :=
  mul_div_mul_right _ _ hF

/-- 経路が違う場合：(W·O·2⁶⁴) / (W·O·2¹²⁸) ≤ 2⁻⁶²。 -/
theorem ratio_cross (W O : ℚ) (hW : 0 < W) (hO : 0 < O) :
    W * O * 2 ^ 64 / (W * O * 2 ^ 128) ≤ 1 / 2 ^ 62 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := mul_pos hW hO
  nlinarith

/-! ### 主定理 -/

/-- **v2c（経路ごとの fin）の 1KB 以下の ε。** 違う 2 入力（どちらも 1024 バイト以下）について、
鍵 (w, m, fin, fin_mid) が一様なら Pr[衝突] ≤ 2⁻⁶²。 -/
theorem le1K_eps (s s' : Bytes) (hs : s.length ≤ 1024) (hs' : s'.length ≤ 1024) (hne : s ≠ s') :
    ((((univ ×ˢ odd128) ×ˢ (univ : Finset Fins)).filter fun p : (Words × ℕ) × Fins =>
        hash1K p.1.1 p.1.2 p.2 s = hash1K p.1.1 p.1.2 p.2 s').card : ℚ) /
      (Fintype.card Words * odd128.card * Fintype.card Fins) ≤ 1 / 2 ^ 62 := by
  classical
  -- 鍵の数 (2⁶⁴)¹³⁰ は simp / push_cast に展開させない（展開するとメモリを使い切る）
  have hW : (0 : ℚ) < Fintype.card Words := Nat.cast_pos.mpr Fintype.card_pos
  have hO : (0 : ℚ) < odd128.card := Nat.cast_pos.mpr (by rw [card_odd128]; positivity)
  have hF : (Fintype.card Fins : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by rw [card_fins]; positivity)
  -- 経路が違う場合：(w, m) ごとに 2⁶⁴ 組
  have cross : ∀ (P : (Words × ℕ) → Fins → Prop) [∀ x, DecidablePred (P x)],
      (∀ x, (univ.filter (P x)).card = 2 ^ 64) →
      ((((univ ×ˢ odd128) ×ˢ (univ : Finset Fins)).filter fun p => P p.1 p.2).card : ℚ) /
        (Fintype.card Words * odd128.card * Fintype.card Fins) ≤ 1 / 2 ^ 62 := by
    intro P _ hP
    rw [card_prod_each _ P _ fun x _ => hP x, Finset.card_product, Finset.card_univ, card_fins,
      Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
    exact ratio_cross _ _ hW hO
  by_cases ha : s.length ≤ 32 <;> by_cases hb : s'.length ≤ 32
  · -- 両方 経路 A
    have h3 := card_prod_const (univ ×ˢ odd128)
      (fun (x : Words × ℕ) (f : Fins) => hash1K x.1 x.2 f s = hash1K x.1 x.2 f s')
      (fun x : Words × ℕ => preA (eA x.1) x.2 s = preA (eA x.1) x.2 s')
      fun x _ f => by simp only [hash1K, ha, hb, ↓reduceIte]; exact hashA_eq_iff _ _ _ _ _
    rw [h3]
    rw [card_equiv_keys eA (fun K m => preA K m s = preA K m s'), Nat.cast_mul,
      ratio_cancel _ _ _ _ hF, Fintype.card_congr eA]
    exact (pathA_eps s s' ha hb hne).trans eps_le_target
  · -- s は A、s' は B
    refine cross (fun (x : Words × ℕ) (f : Fins) => hash1K x.1 x.2 f s = hash1K x.1 x.2 f s')
      fun x => ?_
    have e : (univ.filter fun f : Fins => hash1K x.1 x.2 f s = hash1K x.1 x.2 f s') =
        univ.filter fun f : Fins => out f.1 (preA (eA x.1) x.2 s) = out f.2 (preB (eB x.1) x.2 s') :=
      Finset.filter_congr fun f _ => by simp only [hash1K, ha, hb, ↓reduceIte, hashA, hashB]
    rw [e, card_out_collide]
  · -- s は B、s' は A
    refine cross (fun (x : Words × ℕ) (f : Fins) => hash1K x.1 x.2 f s = hash1K x.1 x.2 f s')
      fun x => ?_
    have e : (univ.filter fun f : Fins => hash1K x.1 x.2 f s = hash1K x.1 x.2 f s') =
        univ.filter fun f : Fins => out f.1 (preA (eA x.1) x.2 s') = out f.2 (preB (eB x.1) x.2 s) :=
      Finset.filter_congr fun f _ => by
        simp only [hash1K, ha, hb, ↓reduceIte, hashA, hashB]; exact eq_comm
    rw [e, card_out_collide]
  · -- 両方 経路 B
    have h3 := card_prod_const (univ ×ˢ odd128)
      (fun (x : Words × ℕ) (f : Fins) => hash1K x.1 x.2 f s = hash1K x.1 x.2 f s')
      (fun x : Words × ℕ => preB (eB x.1) x.2 s = preB (eB x.1) x.2 s')
      fun x _ f => by simp only [hash1K, ha, hb, ↓reduceIte]; exact hashB_eq_iff _ _ _ _ _
    rw [h3]
    rw [card_equiv_keys eB (fun K m => preB K m s = preB K m s'), Nat.cast_mul,
      ratio_cancel _ _ _ _ hF, Fintype.card_congr eB]
    exact (pathB_eps s s' (by omega) hs hs' hne).trans eps_le_target

end LeanHash.Props
