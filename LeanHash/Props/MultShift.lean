/-
P2 残り 3：multiply-shift（Dietzfelbinger）の 2^(1−l)-AU。

ms_a(x) = (a·x mod 2ʷ) を上位 l ビットに落としたもの（a は奇数）。v2c では w = 128、l = 64 で
`hi64(m · acc mod 2¹²⁸)`。x ≠ y なら、奇数 a 2^(w−1) 通りのうち衝突するのは 2^(w−l) 個以下 → 確率 ≤ 2^(1−l)。

証明（数え上げ）:
1. d = x − y = 2ᵗ·u（u は奇数、t < w）、r = a·d mod 2ʷ = 2ᵗ·z、z = a·u mod 2^(w−t) は奇数
2. 衝突（上位 l ビットが同じ）なら、r は 0 の近く：r < B か r > 2ʷ − B（B = 2^(w−l)）
3. t ≥ w − l なら 2 は起こらない（r は 2ᵗ 以上、2ʷ − 2ᵗ 以下）。衝突 0 個
4. t < w − l なら z < R か z > 2^(w−t) − R（R = 2^(w−l−t)）。a ↦ (a の上位 t ビット, g(z)) が単射で、
   値は 2ᵗ × R 通り以下。u が奇数なので z から a mod 2^(w−t) が決まるのが単射の理由
-/
import Mathlib

namespace LeanHash.Props

open Finset

/-- multiply-shift：a·x mod 2ʷ の上位 l ビット。 -/
def ms (w l a x : ℕ) : ℕ := (a * x % 2 ^ w) / 2 ^ (w - l)

/-- 同じ桶（p / B = q / B）なら差は B 未満。 -/
theorem same_bucket {p q B : ℕ} (h : p / B = q / B) (hB : 0 < B) : p < q + B ∧ q < p + B := by
  have h1 := Nat.mod_add_div p B
  have h2 := Nat.mod_add_div q B
  have h3 := Nat.mod_lt p hB
  have h4 := Nat.mod_lt q hB
  rw [h] at h1
  omega

/-- p = (q + r) mod M で p, q の差が B 未満なら、r は 0 の近く（r < B か r > M − B）。 -/
theorem near_zero {M B q r p : ℕ} (hq : q < M) (hr : r < M) (hp : p = (q + r) % M)
    (hb : p < q + B ∧ q < p + B) : r < B ∨ M - B < r := by
  by_cases hc : q + r < M
  · rw [Nat.mod_eq_of_lt hc] at hp; omega
  · have : (q + r) % M = q + r - M := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- 0 の近くにある奇数 z を [0, R) に詰める。 -/
def packNear (N R z : ℕ) : ℕ := if z < R then z / 2 else (z - (N - R)) / 2 + R / 2

theorem packNear_lt {N R z : ℕ} (hN : N % 2 = 0) (hR : R % 2 = 0) (hz : z % 2 = 1) (hzN : z < N)
    (hc : z < R ∨ N - R < z) : packNear N R z < R := by
  unfold packNear; split_ifs <;> omega

theorem packNear_inj {N R z z' : ℕ} (hN : N % 2 = 0) (hR : R % 2 = 0) (_h2R : 2 * R ≤ N)
    (hz : z % 2 = 1) (hz' : z' % 2 = 1) (hzN : z < N) (_hzN' : z' < N)
    (hc : z < R ∨ N - R < z) (hc' : z' < R ∨ N - R < z') (e : packNear N R z = packNear N R z') :
    z = z' := by
  unfold packNear at e; split_ifs at e <;> omega

theorem two_pow_even {k : ℕ} (hk : 0 < k) : 2 ^ k % 2 = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  simp [pow_succ]

/-- 衝突する a について：r = a·d mod 2ʷ = 2ᵗ·z（z = a·u mod 2^(w−t)）は 0 の近く。 -/
theorem collide_near {w l a x y t u : ℕ} (_hx : x < 2 ^ w) (_hy : y < 2 ^ w) (hlt : y < x)
    (hd : x - y = 2 ^ t * u) (ht : t ≤ w)
    (hc : ms w l a x = ms w l a y) :
    2 ^ t * (a * u % 2 ^ (w - t)) < 2 ^ (w - l) ∨
      2 ^ w - 2 ^ (w - l) < 2 ^ t * (a * u % 2 ^ (w - t)) := by
  have hM : 2 ^ w = 2 ^ t * 2 ^ (w - t) := by rw [← pow_add]; congr 1; omega
  have hr : a * (x - y) % 2 ^ w = 2 ^ t * (a * u % 2 ^ (w - t)) := by
    rw [hd, hM, ← mul_assoc, mul_comm a, mul_assoc, Nat.mul_mod_mul_left]
  rw [← hr]
  have hpos : 0 < 2 ^ w := by positivity
  refine near_zero (q := a * y % 2 ^ w) (p := a * x % 2 ^ w) (Nat.mod_lt _ hpos)
    (Nat.mod_lt _ hpos) ?_ (same_bucket hc (by positivity))
  rw [← Nat.add_mod, ← mul_add]
  congr 2
  omega

/-- **multiply-shift は 2^(1−l)-AU。** x ≠ y（どちらも 2ʷ 未満）なら、衝突する奇数 a は 2^(w−l) 個以下
（奇数は全部で 2^(w−1) 個）。 -/
theorem ms_au (w l : ℕ) (hl : 1 ≤ l) (hlw : l ≤ w) (x y : ℕ) (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (hxy : x ≠ y) :
    ((range (2 ^ w)).filter fun a => a % 2 = 1 ∧ ms w l a x = ms w l a y).card ≤ 2 ^ (w - l) := by
  wlog hlt : y < x generalizing x y
  · have e : ((range (2 ^ w)).filter fun a => a % 2 = 1 ∧ ms w l a x = ms w l a y) =
        (range (2 ^ w)).filter fun a => a % 2 = 1 ∧ ms w l a y = ms w l a x :=
      Finset.filter_congr fun a _ => by rw [eq_comm (a := ms w l a x)]
    rw [e]
    exact this y x hy hx (Ne.symm hxy) (by omega)
  obtain ⟨t, u, hu, hd⟩ := Nat.exists_eq_two_pow_mul_odd (n := x - y) (by omega)
  have hu1 : 1 ≤ u := hu.pos
  have h2t : 2 ^ t ≤ x - y := hd ▸ Nat.le_mul_of_pos_right _ hu.pos
  have ht : t < w := by
    by_contra h
    have : 2 ^ w ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set N := 2 ^ (w - t) with hN
  set P := 2 ^ t with hP
  have hM : 2 ^ w = P * N := by rw [hP, hN, ← pow_add]; congr 1; omega
  have hNe : N % 2 = 0 := two_pow_even (by omega)
  have hPpos : 0 < P := by positivity
  -- z は奇数で N 未満
  have hzodd : ∀ a, a % 2 = 1 → a * u % N % 2 = 1 := fun a ha => by
    rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hNe), Nat.mul_mod, ha,
      Nat.odd_iff.mp hu]
  have hzlt : ∀ a, a * u % N < N := fun a => Nat.mod_lt _ (by positivity)
  by_cases htl : w - l ≤ t
  · -- 衝突は起こらない
    have hB : 2 ^ (w - l) ≤ P := Nat.pow_le_pow_right (by norm_num) htl
    suffices h : (range (2 ^ w)).filter (fun a => a % 2 = 1 ∧ ms w l a x = ms w l a y) = ∅ by
      simp [h]
    apply Finset.filter_false_of_mem
    rintro a - ⟨ha, hc⟩
    have hn := collide_near hx hy hlt hd ht.le hc
    rw [← hP, ← hN, hM] at hn
    have z1 : 1 ≤ a * u % N := by have := hzodd a ha; omega
    have hlo : P ≤ P * (a * u % N) := Nat.le_mul_of_pos_right _ z1
    have hhi : P * (a * u % N) ≤ P * (N - 1) := Nat.mul_le_mul_left _ (by have := hzlt a; omega)
    have hhi' : P * (N - 1) = P * N - P := Nat.mul_sub_one P N
    have hPN : P ≤ P * N := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  · push Not at htl
    set R := 2 ^ (w - l - t) with hR
    have hB : 2 ^ (w - l) = P * R := by rw [hP, hR, ← pow_add]; congr 1; omega
    have hRe : R % 2 = 0 := two_pow_even (by omega)
    have h2R : 2 * R ≤ N := by
      rw [hR, hN, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    -- 衝突する a では z が 0 の近く
    have hnear : ∀ a, a % 2 = 1 → ms w l a x = ms w l a y →
        a * u % N < R ∨ N - R < a * u % N := fun a ha hc => by
      have hn := collide_near hx hy hlt hd ht.le hc
      rw [← hP, ← hN, hB, hM] at hn
      rcases hn with h | h
      · exact Or.inl (Nat.lt_of_mul_lt_mul_left h)
      · right
        rw [← Nat.mul_sub] at h
        exact Nat.lt_of_mul_lt_mul_left h
    -- a ↦ (a / N, packNear (a·u mod N)) が単射
    have hcard := Finset.card_le_card_of_injOn
      (s := (range (2 ^ w)).filter fun a => a % 2 = 1 ∧ ms w l a x = ms w l a y)
      (t := range P ×ˢ range R) (fun a => (a / N, packNear N R (a * u % N))) ?_ ?_
    · simpa [Finset.card_product, hB] using hcard
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha
      simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
      refine ⟨Nat.div_lt_of_lt_mul (by rw [mul_comm, ← hM]; exact ha.1), ?_⟩
      exact packNear_lt hNe hRe (hzodd a ha.2.1) (hzlt a) (hnear a ha.2.1 ha.2.2)
    · intro a ha a' ha' e
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha ha'
      simp only [Prod.mk.injEq] at e
      have hz := packNear_inj hNe hRe h2R (hzodd a ha.2.1) (hzodd a' ha'.2.1) (hzlt a) (hzlt a')
        (hnear a ha.2.1 ha.2.2) (hnear a' ha'.2.1 ha'.2.2) e.2
      -- u は奇数なので N と互いに素。a·u ≡ a'·u から a ≡ a'（mod N）
      have hcop : Nat.Coprime N u := by
        rw [hN]; exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hu)
      have hmod : a % N = a' % N := Nat.ModEq.cancel_right_of_coprime hcop hz
      have h1 := Nat.mod_add_div a N
      have h2 := Nat.mod_add_div a' N
      rw [hmod, e.1] at h1
      omega

/-- 2ʷ 未満の奇数は 2^(w−1) 個。 -/
theorem card_odd {w : ℕ} (hw : 0 < w) :
    ((range (2 ^ w)).filter fun a => a % 2 = 1).card = 2 ^ (w - 1) := by
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
  have e : ((range (2 ^ w)).filter fun a => a % 2 = 1) =
      (range (2 ^ (w - 1))).image fun j => 2 * j + 1 := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    rw [h2]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨a / 2, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega
  rw [e, Finset.card_image_of_injective _ (fun i j h => by have : 2 * i + 1 = 2 * j + 1 := h; omega),
    Finset.card_range]

/-- 確率の形：奇数 a について Pr[ms_a(x) = ms_a(y)] ≤ 2^(1−l)。 -/
theorem ms_au_prob (w l : ℕ) (hl : 1 ≤ l) (hlw : l ≤ w) (x y : ℕ) (hx : x < 2 ^ w)
    (hy : y < 2 ^ w) (hxy : x ≠ y) :
    (((range (2 ^ w)).filter fun a => a % 2 = 1 ∧ ms w l a x = ms w l a y).card : ℚ) /
      ((range (2 ^ w)).filter fun a => a % 2 = 1).card ≤ 2 / 2 ^ l := by
  have hc := ms_au w l hl hlw x y hx hy hxy
  rw [card_odd (by omega), div_le_div_iff₀ (by positivity) (by positivity)]
  have hw : (2 : ℚ) ^ (w - l) * 2 ^ l = 2 * 2 ^ (w - 1) := by
    rw [← pow_add, ← pow_succ']; congr 1; omega
  calc _ ≤ ((2 ^ (w - l) : ℕ) : ℚ) * 2 ^ l := by gcongr
    _ = _ := by exact_mod_cast hw

end LeanHash.Props
