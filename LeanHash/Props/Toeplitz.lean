/-
P2 残り 1：レーンの有無つきの NH（1 本）と、鍵を 1 組ずらした Toeplitz 2 本の ε。

v2c では、長さによって組（レーン）の数が変わる。ない組は和に何も足さない（0 埋めの組とは違う）ので、
メッセージを `Fin n → Option (Fin W × Fin W)` で表す。長さの組は長さによらず最後の位置にある。

証明は「1 か所の鍵をずらす写像が単射」という数え上げ（`nh_eau` と同じ形）を抽象化して使う:
- `card_single`：差の和 Σ Dᵢ(Kᵢ) = 0 となる鍵の数 × |T| ≤ 鍵の総数（位置 j の D_j がずらし s について単射なら）
- `card_toeplitz`：2 本目は鍵を 1 つずらす（Kᵢ₊₁）。j より後ろの差が 0 なら、j と j+1 の 2 か所をずらして |T|² 倍

Toeplitz の要点：j を「値が違う最後の位置」に取ると、K_{j+1} は 2 本目の位置 j にしか効かない。
1 本目で K_j が決まり、その後 2 本目で K_{j+1} が決まる。
-/
import LeanHash.Props.NH

namespace LeanHash.Props

open LeanHash.Spec Finset

section Abstract

variable {P T Q : Type*} [AddCommGroup Q]

/-- 差関数 D が、ずらし s について単射：ずらした結果が同じで D の値も同じなら、元の鍵もずらし幅も同じ。 -/
def ShiftInj (D : P → Q) (s : P → T → P) : Prop :=
  ∀ k k' t t', s k t = s k' t' → D k = D k' → k = k' ∧ t = t'

/-- 和が両方 0 で、j 以外の項が等しければ、j の項も等しい。 -/
theorem term_eq_of_sum_zero {n : ℕ} (f g : Fin n → Q) (j : Fin n)
    (hf : ∑ i, f i = 0) (hg : ∑ i, g i = 0) (hfg : ∀ i, i ≠ j → f i = g i) : f j = g j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hf hg
  have : ∑ i ∈ univ.erase j, f i = ∑ i ∈ univ.erase j, g i :=
    Finset.sum_congr rfl fun i hi => hfg i (Finset.ne_of_mem_erase hi)
  rw [this] at hf
  exact add_right_cancel (hf.trans hg.symm)

variable [Fintype P] [Fintype T] [DecidableEq Q]

/-- **1 本版の数え上げ。** 位置 j の差関数がずらしについて単射なら、Σ Dᵢ(Kᵢ) = 0 の鍵の数 × |T| ≤ 鍵の総数。 -/
theorem card_single {n : ℕ} (D : Fin n → P → Q) (j : Fin n) (s : P → T → P)
    (hs : ShiftInj (D j) s) :
    (univ.filter fun K : Fin n → P => ∑ i, D i (K i) = 0).card * Fintype.card T ≤
      Fintype.card (Fin n → P) := by
  refine card_mul_le_of_inj _ (fun K t => Function.update K j (s (K j) t)) ?_
  intro K hK K' hK' t t' e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK hK'
  have hag : ∀ i, i ≠ j → K i = K' i := fun i hi => by
    simpa [Function.update_of_ne hi] using congrFun e i
  have hj : s (K j) t = s (K' j) t' := by simpa using congrFun e j
  have hD : D j (K j) = D j (K' j) :=
    term_eq_of_sum_zero (fun i => D i (K i)) (fun i => D i (K' i)) j hK hK'
      fun i hi => by rw [hag i hi]
  obtain ⟨h1, h2⟩ := hs _ _ _ _ hj hD
  refine ⟨funext fun i => ?_, h2⟩
  by_cases hi : i = j
  · subst hi; exact h1
  · exact hag i hi

/-- **Toeplitz 2 本版の数え上げ。** 1 本目は鍵 K_i、2 本目は K_{i+1}。
位置 j の差関数がずらしについて単射で、j より後ろの差が 0 なら、両方とも 0 になる鍵の数 × |T|² ≤ 鍵の総数。 -/
theorem card_toeplitz {n : ℕ} (D : Fin n → P → Q) (j : Fin n)
    (hz : ∀ i, j < i → ∀ k, D i k = 0) (s : P → T → P) (hs : ShiftInj (D j) s) :
    (univ.filter fun K : Fin (n + 1) → P =>
        ∑ i, D i (K i.castSucc) = 0 ∧ ∑ i, D i (K i.succ) = 0).card *
        Fintype.card (T × T) ≤
      Fintype.card (Fin (n + 1) → P) := by
  have hne : j.castSucc ≠ j.succ := Fin.castSucc_lt_succ.ne
  refine card_mul_le_of_inj _ (fun K t => Function.update
    (Function.update K j.castSucc (s (K j.castSucc) t.1)) j.succ (s (K j.succ) t.2)) ?_
  rintro K hK K' hK' ⟨t1, t2⟩ ⟨t1', t2'⟩ e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK hK'
  have hag : ∀ i, i ≠ j.castSucc → i ≠ j.succ → K i = K' i := fun i h1 h2 => by
    simpa [Function.update_of_ne h1, Function.update_of_ne h2] using congrFun e i
  have e2 : s (K j.succ) t2 = s (K' j.succ) t2' := by simpa using congrFun e j.succ
  have e1 : s (K j.castSucc) t1 = s (K' j.castSucc) t1' := by
    simpa [Function.update_of_ne hne] using congrFun e j.castSucc
  -- 1 本目：j 以外の項は、j より前なら鍵が同じ、後ろなら 0
  have hD1 : D j (K j.castSucc) = D j (K' j.castSucc) := by
    refine term_eq_of_sum_zero (fun i => D i (K i.castSucc)) (fun i => D i (K' i.castSucc)) j
      hK.1 hK'.1 fun i hi => ?_
    rcases lt_or_gt_of_ne hi with h | h
    · rw [hag i.castSucc (fun e => hi (Fin.castSucc_injective _ e))
        (fun e => by have := congrArg Fin.val e; simp at this; omega)]
    · simp [hz i h]
  obtain ⟨k1, rfl⟩ := hs _ _ _ _ e1 hD1
  have hag' : ∀ i, i ≠ j.succ → K i = K' i := fun i hi => by
    by_cases h : i = j.castSucc
    · subst h; exact k1
    · exact hag i h hi
  -- 2 本目：j 以外の項は、鍵がすべて同じ
  have hD2 : D j (K j.succ) = D j (K' j.succ) :=
    term_eq_of_sum_zero (fun i => D i (K i.succ)) (fun i => D i (K' i.succ)) j hK.2 hK'.2
      fun i hi => by rw [hag' i.succ (fun e => hi (Fin.succ_injective _ e))]
  obtain ⟨k2, rfl⟩ := hs _ _ _ _ e2 hD2
  refine ⟨funext fun i => ?_, rfl⟩
  by_cases h : i = j.succ
  · subst h; exact k2
  · exact hag' i h

end Abstract

variable {W n : ℕ}

/-- 1 組の差 `pd a a'`（a ≠ a'）は、違う語に対応しない方の鍵をずらすと単射。 -/
def pdShift (a a' : Fin W × Fin W) : (Fin W × Fin W) → Fin W → Fin W × Fin W :=
  if a.1 ≠ a'.1 then fun k t => (k.1, k.2 + t) else fun k t => (k.1 + t, k.2)

theorem pd_shiftInj {a a' : Fin W × Fin W} (h : a ≠ a') : ShiftInj (pd a a') (pdShift a a') := by
  intro k k' t t' e hD
  unfold pdShift at e
  split_ifs at e with h1
  · simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    have h2 : k.2 = k'.2 := by
      apply pd_inj2 h1 k.1
      simp only
      conv_rhs => rw [e1]
      exact hD
    exact ⟨Prod.ext e1 h2, add_left_cancel (h2 ▸ e2)⟩
  · push Not at h1
    have h2' : a.2 ≠ a'.2 := fun e' => h (Prod.ext h1 e')
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    have h1' : k.1 = k'.1 := by
      apply pd_inj1 h2' k.2
      simp only
      conv_rhs => rw [e2]
      exact hD
    exact ⟨Prod.ext h1' e2, add_left_cancel (h1' ▸ e1)⟩

/-- 有無つきの組の値（ない組は 0）。 -/
def termO (o : Option (Fin W × Fin W)) (k : Fin W × Fin W) : ZMod (W ^ 2) :=
  match o with
  | none => 0
  | some m => (pairVal m k : ZMod (W ^ 2))

/-- 有無つきの NH（1 本）。 -/
def nhO (K : Fin n → Fin W × Fin W) (M : Fin n → Option (Fin W × Fin W)) : ZMod (W ^ 2) :=
  ∑ i, termO (M i) (K i)

/-- Toeplitz 2 本の NH。1 本目はレーン i に鍵 i、2 本目は鍵 i+1。 -/
def nhT (K : Fin (n + 1) → Fin W × Fin W) (M : Fin n → Option (Fin W × Fin W)) :
    ZMod (W ^ 2) × ZMod (W ^ 2) :=
  (∑ i, termO (M i) (K i.castSucc), ∑ i, termO (M i) (K i.succ))

/-- 位置ごとの差。 -/
def dO (M M' : Fin n → Option (Fin W × Fin W)) (i : Fin n) (k : Fin W × Fin W) : ZMod (W ^ 2) :=
  termO (M i) k - termO (M' i) k

theorem dO_eq_pd {M M' : Fin n → Option (Fin W × Fin W)} {j : Fin n} {a a' : Fin W × Fin W}
    (ha : M j = some a) (ha' : M' j = some a') : dO M M' j = pd a a' := by
  funext k; simp [dO, ha, ha', termO, pd]

theorem dO_eq_zero {M M' : Fin n → Option (Fin W × Fin W)} {i : Fin n} (h : M i = M' i)
    (k : Fin W × Fin W) : dO M M' i k = 0 := by
  simp [dO, h]

theorem sum_dO (M M' : Fin n → Option (Fin W × Fin W)) (K : Fin n → Fin W × Fin W) :
    ∑ i, termO (M i) (K i) - ∑ i, termO (M' i) (K i) = ∑ i, dO M M' i (K i) := by
  simp [dO, Finset.sum_sub_distrib]

/-- 「両方にあって値が違う位置 j」：j に違う組があり、j より後ろは同じ。 -/
def LastDiff (M M' : Fin n → Option (Fin W × Fin W)) (j : Fin n) : Prop :=
  (∃ a a', M j = some a ∧ M' j = some a' ∧ a ≠ a') ∧ ∀ i, j < i → M i = M' i

/-- **有無つき NH（1 本）は (1/W)-AU。** 両方にあって値が違う組が 1 つでもあれば、衝突する鍵の数 × W ≤ W^(2n)。 -/
theorem nhO_eau (M M' : Fin n → Option (Fin W × Fin W)) (j : Fin n) {a a' : Fin W × Fin W}
    (ha : M j = some a) (ha' : M' j = some a') (hne : a ≠ a') :
    (univ.filter fun K => nhO K M = nhO K M').card * W ≤ W ^ (2 * n) := by
  classical
  have h := card_single (dO M M') j (pdShift a a') (by rw [dO_eq_pd ha ha']; exact pd_shiftInj hne)
  rw [Fintype.card_fin, card_keys] at h
  have hset : (univ.filter fun K => nhO K M = nhO K M') =
      univ.filter fun K => ∑ i, dO M M' i (K i) = 0 := by
    apply Finset.filter_congr
    intro K _
    rw [← sum_dO, sub_eq_zero]
    rfl
  rw [hset]
  exact h

/-- **Toeplitz 2 本は (1/W²)-AU。** 値が違う最後の組が両方にあれば、2 本とも衝突する鍵の数 × W² ≤ W^(2(n+1))。 -/
theorem nhT_eau (M M' : Fin n → Option (Fin W × Fin W)) (j : Fin n) (hj : LastDiff M M' j) :
    (univ.filter fun K => nhT K M = nhT K M').card * W ^ 2 ≤ W ^ (2 * (n + 1)) := by
  classical
  obtain ⟨⟨a, a', ha, ha', hne⟩, hlast⟩ := hj
  have h := card_toeplitz (dO M M') j (fun i hi k => dO_eq_zero (hlast i hi) k) (pdShift a a')
    (by rw [dO_eq_pd ha ha']; exact pd_shiftInj hne)
  rw [Fintype.card_prod, Fintype.card_fin, card_keys, ← sq] at h
  have hset : (univ.filter fun K => nhT K M = nhT K M') =
      univ.filter fun K : Fin (n + 1) → Fin W × Fin W =>
        ∑ i, dO M M' i (K i.castSucc) = 0 ∧ ∑ i, dO M M' i (K i.succ) = 0 := by
    apply Finset.filter_congr
    intro K _
    rw [nhT, nhT, Prod.mk.injEq, ← sum_dO, ← sum_dO, sub_eq_zero, sub_eq_zero]
  rw [hset]
  exact h

/-- 有無が同じ位置にそろった 2 つの違うメッセージには、`LastDiff` となる位置がある。 -/
theorem exists_lastDiff (M M' : Fin n → Option (Fin W × Fin W)) (hne : M ≠ M')
    (hsome : ∀ i, (M i).isSome = (M' i).isSome) : ∃ j, LastDiff M M' j := by
  classical
  have hS : (univ.filter fun i => M i ≠ M' i).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, by simpa using hi⟩
  set j := (univ.filter fun i => M i ≠ M' i).max' hS
  have hjmem := Finset.max'_mem _ hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
  refine ⟨j, ?_, fun i hi => ?_⟩
  · have hs := hsome j
    cases hM : M j with
    | none =>
      cases hM' : M' j with
      | none => exact absurd (hM.trans hM'.symm) hjmem
      | some b => simp [hM, hM'] at hs
    | some a =>
      cases hM' : M' j with
      | none => simp [hM, hM'] at hs
      | some b => exact ⟨a, b, rfl, rfl, fun e => hjmem (by rw [hM, hM', e])⟩
  · by_contra h
    have := Finset.le_max' (univ.filter fun i => M i ≠ M' i) i (by simp [h])
    exact absurd hi (not_lt.mpr this)

end LeanHash.Props
