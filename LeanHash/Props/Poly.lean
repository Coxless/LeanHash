/-
P2.5 多項式段：素数 q を法とする多項式ハッシュ（Horner）の ε-AU。

- `horner r [c₀, …, c_ℓ] = c₀·r^ℓ + … + c_ℓ`（Rust の `horner` を先頭から繰り返したもの。初期値 0）
- `horner_au`：係数列が「長さが同じで違う」か「最後の係数（定数項）が違う」なら、
  衝突する r は ℓ 個以下（ℓ は長いほうの列の長さ − 1）。r が一様なら Pr ≤ ℓ/q
- 証明は「差の多項式は 0 でなく、次数 ≤ ℓ なので根は ℓ 個以下」（`Polynomial.card_roots'`）
- q = 2⁶¹ − 1 が素数であることは Lucas–Lehmer（`p61_prime`）
-/
import Mathlib

namespace LeanHash.Props

open Finset Polynomial

/-- p = 2⁶¹ − 1（Rust の `P`）。 -/
abbrev P61 : ℕ := 2 ^ 61 - 1

/-- **2⁶¹ − 1 は素数**（Mathlib の Lucas–Lehmer 判定）。 -/
theorem p61_prime : Nat.Prime P61 := lucas_lehmer_sufficiency 61 (by norm_num) (by norm_num)

instance : Fact (Nat.Prime P61) := ⟨p61_prime⟩

variable {q : ℕ} [Fact q.Prime]

/-- Horner 法（係数は先頭から。初期値 0）。 -/
def horner (r : ZMod q) (l : List (ZMod q)) : ZMod q := l.foldl (fun h c => h * r + c) 0

/-- 逆順の係数列（先頭が定数項）の多項式 Σ bᵢ Xⁱ。 -/
noncomputable def rpoly : List (ZMod q) → (ZMod q)[X]
  | [] => 0
  | c :: l => C c + X * rpoly l

theorem coeff_rpoly (l : List (ZMod q)) (m : ℕ) : (rpoly l).coeff m = l.getD m 0 := by
  induction l generalizing m with
  | nil => simp [rpoly]
  | cons c l ih =>
    cases m with
    | zero => simp [rpoly]
    | succ m => simp [rpoly, coeff_X_mul, ih]

theorem eval_rpoly (r : ZMod q) (l : List (ZMod q)) :
    (rpoly l).eval r = l.foldr (fun c h => h * r + c) 0 := by
  induction l with
  | nil => simp [rpoly]
  | cons c l ih => simp only [rpoly, eval_add, eval_C, eval_mul, eval_X, ih, List.foldr_cons]; ring

theorem horner_eq_eval (r : ZMod q) (l : List (ZMod q)) : horner r l = (rpoly l.reverse).eval r := by
  rw [eval_rpoly, horner, List.foldl_eq_foldr_reverse]

theorem degree_rpoly_lt (l : List (ZMod q)) : (rpoly l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_rpoly, List.getD_eq_default _ _ hm]

/-- 長さが同じで違う係数列の多項式は違う。 -/
theorem rpoly_ne_of_length {b b' : List (ZMod q)} (hlen : b.length = b'.length) (hne : b ≠ b') :
    rpoly b ≠ rpoly b' := by
  intro h
  apply hne
  apply List.ext_getElem hlen
  intro i hi hi'
  have := congrArg (fun f => f.coeff i) h
  simp only [coeff_rpoly, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at this
  exact this

/-- 定数項が違えば多項式は違う。 -/
theorem rpoly_ne_of_head {c c' : ZMod q} (l l' : List (ZMod q)) (h : c ≠ c') :
    rpoly (c :: l) ≠ rpoly (c' :: l') := by
  intro e
  have := congrArg (fun f => f.coeff 0) e
  simp only [coeff_rpoly, List.getD_cons_zero] at this
  exact h this

/-- **根の個数。** 違う 2 つの多項式（次数 ≤ n）の値が一致する点は n 個以下。 -/
theorem card_eval_eq_le {f g : (ZMod q)[X]} (hne : f ≠ g) {n : ℕ} (hf : f.degree < (n + 1 : ℕ))
    (hg : g.degree < (n + 1 : ℕ)) : (univ.filter fun r => f.eval r = g.eval r).card ≤ n := by
  classical
  have hd : f - g ≠ 0 := sub_ne_zero.mpr hne
  have hsub : (univ.filter fun r => f.eval r = g.eval r) ⊆ (f - g).roots.toFinset := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rw [Multiset.mem_toFinset, mem_roots hd, IsRoot.def, eval_sub, hr, sub_self]
  have hdeg : (f - g).natDegree < n + 1 :=
    (natDegree_lt_iff_degree_lt hd).mpr ((degree_sub_le f g).trans_lt (max_lt hf hg))
  calc _ ≤ (f - g).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (f - g).roots := Multiset.toFinset_card_le _
    _ ≤ (f - g).natDegree := card_roots' _
    _ ≤ n := Nat.lt_succ_iff.mp hdeg

/-- **多項式ハッシュの ε-AU（逆順の係数列で）。** 列の長さ ≤ n + 1 で多項式が違えば、衝突する r は n 個以下。 -/
theorem rpoly_au {b b' : List (ZMod q)} {n : ℕ} (hb : b.length ≤ n + 1) (hb' : b'.length ≤ n + 1)
    (hne : rpoly b ≠ rpoly b') :
    (univ.filter fun r => (rpoly b).eval r = (rpoly b').eval r).card ≤ n :=
  card_eval_eq_le hne ((degree_rpoly_lt b).trans_le (by exact_mod_cast hb))
    ((degree_rpoly_lt b').trans_le (by exact_mod_cast hb'))

/-- **Horner の ε-AU。** 係数列 a ++ [c] と a' ++ [c']（長さ ≤ n + 1）について、
「長さが同じで違う」か「最後の係数が違う」なら、衝突する r は n 個以下（Pr ≤ n/q）。 -/
theorem horner_au {a a' : List (ZMod q)} {c c' : ZMod q} {n : ℕ} (hb : a.length ≤ n)
    (hb' : a'.length ≤ n)
    (hne : (a.length = a'.length ∧ a ++ [c] ≠ a' ++ [c']) ∨ c ≠ c') :
    (univ.filter fun r => horner r (a ++ [c]) = horner r (a' ++ [c'])).card ≤ n := by
  have e : ∀ r, (horner r (a ++ [c]) = horner r (a' ++ [c'])) ↔
      ((rpoly (c :: a.reverse)).eval r = (rpoly (c' :: a'.reverse)).eval r) := fun r => by
    rw [horner_eq_eval, horner_eq_eval, List.reverse_append, List.reverse_append]
    rfl
  rw [Finset.filter_congr fun r _ => e r]
  refine rpoly_au (by simp; omega) (by simp; omega) ?_
  rcases hne with ⟨hlen, hne⟩ | hc
  · refine rpoly_ne_of_length (by simp [hlen]) fun h => hne ?_
    have := congrArg List.reverse h
    simpa [List.reverse_append] using this
  · exact rpoly_ne_of_head _ _ hc

end LeanHash.Props
