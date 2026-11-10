/-
P2 のまとめ：v2c の 1KB 以下の 2 経路で、同じ経路に入る違う 2 入力の衝突確率 ≤ 2⁻⁶⁴ + 2⁻⁶³ ≤ 2⁻⁶²。

鍵（すべて独立で一様、入力とも独立）:
- 経路 A: NH の鍵 K（u64 を 130 語 = 64bit 語の組 65 個）、乗数 m（2¹²⁸ 未満の奇数）、fin（u64）
- 経路 B: 同じ 130 語を NH32 の鍵レーン 130 個（各レーン = 32bit 語の組）として読む

流れ（`rust/leanhash/src/v2.rs` の `hash` / `hash_c`）:
  バイト列 ─(Encode)→ 組の並び ─(NH)→ acc（128bit）─(multiply-shift)→ 64bit ─(^ fin, fmix64)→ 出力

ε の内訳:
- NH 段: 経路 A は NH64 1 本で 2⁻⁶⁴（`nhO_eau`）、経路 B は NH32 の Toeplitz 2 本で 2⁻⁶⁴（`nhT_eau`）。
  長さの組（レーン）は長さによらず最後の位置にあるので、長さが違えばそこが「両方にあって値が違う最後の位置」になる
- multiply-shift: 2⁻⁶³（`ms_au`）
- 仕上げ（^ fin、fmix64）: fin ごとに単射なので確率は変わらない（`out_eq_iff`）

経路をまたぐ 2 入力（A と B）は、経路ごとに独立な fin（Rust の `fin` / `fin_mid`）で 2⁻⁶⁴ ちょうど
（`card_out_collide`）。両方をまとめた 1KB 以下の主定理は `Props/Le1K.lean` の `le1K_eps`。
-/
import LeanHash.Spec.Encode
import LeanHash.Props.Toeplitz
import LeanHash.Props.MultShift
import LeanHash.Props.Compose

namespace LeanHash.Props

open Finset LeanHash.Spec

/-- 経路 A の NH 鍵：64bit 語の組 65 個。 -/
abbrev KeyA := Fin 65 → Fin (2 ^ 64) × Fin (2 ^ 64)

/-- 経路 B の NH 鍵：32bit 語の組（= u64 1 語）130 個。 -/
abbrev KeyB := Fin (129 + 1) → Fin (2 ^ 32) × Fin (2 ^ 32)

/-- multiply-shift の乗数：2¹²⁸ 未満の奇数。 -/
def odd128 : Finset ℕ := (range (2 ^ 128)).filter fun a => a % 2 = 1

/-- 経路 A の acc（128bit）。 -/
def accA (K : KeyA) (s : Bytes) : ℕ := (nhO K (msgA s)).val

/-- 経路 B の acc：2 本の出力 (x, y) を y·2⁶⁴ + x にまとめる。 -/
def accB (K : KeyB) (s : Bytes) : ℕ := (nhT K (msgB s)).1.val + 2 ^ 64 * (nhT K (msgB s)).2.val

/-- multiply-shift まで（`ms(m, acc) = hi64(m·acc mod 2¹²⁸)`）。 -/
def preA (K : KeyA) (m : ℕ) (s : Bytes) : ℕ := ms 128 64 m (accA K s)
def preB (K : KeyB) (m : ℕ) (s : Bytes) : ℕ := ms 128 64 m (accB K s)

/-- 出力（v2c の `fmix64(ms(m, acc) ^ fin)`）。 -/
def hashA (K : KeyA) (m : ℕ) (fin : BitVec 64) (s : Bytes) : BitVec 64 := out fin (preA K m s)
def hashB (K : KeyB) (m : ℕ) (fin : BitVec 64) (s : Bytes) : BitVec 64 := out fin (preB K m s)

/-! ### 値の範囲 -/

theorem accA_lt (K : KeyA) (s : Bytes) : accA K s < 2 ^ 128 :=
  (ZMod.val_lt _).trans_eq (by norm_num)

theorem accB_lt (K : KeyB) (s : Bytes) : accB K s < 2 ^ 128 := by
  have hx : (nhT K (msgB s)).1.val < 2 ^ 64 := (ZMod.val_lt _).trans_eq (by norm_num)
  have hy : (nhT K (msgB s)).2.val < 2 ^ 64 := (ZMod.val_lt _).trans_eq (by norm_num)
  unfold accB
  omega

theorem accB_eq_iff (K : KeyB) (s s' : Bytes) :
    accB K s = accB K s' ↔ nhT K (msgB s) = nhT K (msgB s') := by
  constructor
  · intro h
    have hx : (nhT K (msgB s)).1.val < 2 ^ 64 := (ZMod.val_lt _).trans_eq (by norm_num)
    have hy : (nhT K (msgB s)).2.val < 2 ^ 64 := (ZMod.val_lt _).trans_eq (by norm_num)
    have hx' : (nhT K (msgB s')).1.val < 2 ^ 64 := (ZMod.val_lt _).trans_eq (by norm_num)
    have hy' : (nhT K (msgB s')).2.val < 2 ^ 64 := (ZMod.val_lt _).trans_eq (by norm_num)
    unfold accB at h
    exact Prod.ext (ZMod.val_injective _ (by omega)) (ZMod.val_injective _ (by omega))
  · intro h; unfold accB; rw [h]

theorem ms_lt (m x : ℕ) : ms 128 64 m x < 2 ^ 64 :=
  Nat.div_lt_of_lt_mul ((Nat.mod_lt _ (by positivity)).trans_eq (by norm_num))

/-- 仕上げ（^ fin、fmix64）は衝突を変えない。 -/
theorem hashA_eq_iff (K : KeyA) (m : ℕ) (fin : BitVec 64) (s s' : Bytes) :
    hashA K m fin s = hashA K m fin s' ↔ preA K m s = preA K m s' :=
  out_eq_iff fin (ms_lt _ _) (ms_lt _ _)

theorem hashB_eq_iff (K : KeyB) (m : ℕ) (fin : BitVec 64) (s s' : Bytes) :
    hashB K m fin s = hashB K m fin s' ↔ preB K m s = preB K m s' :=
  out_eq_iff fin (ms_lt _ _) (ms_lt _ _)

/-! ### 長さの符号化：違う 2 入力には「両方にあって値が違う最後の組」がある -/

theorem msgA_lastDiff {s s' : Bytes} (hs : s.length ≤ 32) (hs' : s'.length ≤ 32) (hne : s ≠ s') :
    ∃ j, LastDiff (msgA s) (msgA s') j := by
  by_cases hlen : s.length = s'.length
  · exact exists_lastDiff _ _ (fun e => hne (msgA_inj hlen hs e)) (msgA_isSome hlen)
  · refine ⟨64, ⟨(wd 64 s.length, wd 64 0), (wd 64 s'.length, wd 64 0), by simp [msgA],
      by simp [msgA], fun e => hlen ?_⟩, fun i hi => ?_⟩
    · have := congrArg Prod.fst e
      exact wd_inj (by omega) (by omega) this
    · exact absurd i.isLt (by have := Fin.lt_def.mp hi; simp at this; omega)

theorem msgB_lastDiff {s s' : Bytes} (hs8 : 8 ≤ s.length) (hs : s.length ≤ 1024)
    (hs' : s'.length ≤ 1024) (hne : s ≠ s') : ∃ j, LastDiff (msgB s) (msgB s') j := by
  by_cases hlen : s.length = s'.length
  · exact exists_lastDiff _ _ (fun e => hne (msgB_inj hlen hs8 hs e)) (msgB_isSome hlen)
  · refine ⟨128, ⟨(wd 32 s.length, wd 32 0), (wd 32 s'.length, wd 32 0), by simp [msgB],
      by simp [msgB], fun e => hlen ?_⟩, fun i hi => ?_⟩
    · have := congrArg Prod.fst e
      exact wd_inj (by omega) (by omega) this
    · exact absurd i.isLt (by have := Fin.lt_def.mp hi; simp at this; omega)

/-! ### multiply-shift の段 -/

theorem card_odd128 : odd128.card = 2 ^ 127 := card_odd (w := 128) (by norm_num)

theorem ms_stage {x y : ℕ} (hx : x < 2 ^ 128) (hy : y < 2 ^ 128) (hxy : x ≠ y) :
    (odd128.filter fun a => ms 128 64 a x = ms 128 64 a y).card ≤ 2 ^ 64 := by
  have h := ms_au 128 64 (by norm_num) (by norm_num) x y hx hy hxy
  rw [odd128, Finset.filter_filter]
  exact h

/-- 2 段の確率の足し算：NH の衝突 c₀·2⁶⁴ ≤ N なら、(K, m) の衝突 ≤ N·2⁶³ + N·2⁶⁴。 -/
theorem two_stage {N c0 coll : ℕ} (hc0 : c0 * 2 ^ 64 ≤ N) (hcoll : coll ≤ c0 * 2 ^ 127 + N * 2 ^ 64) :
    (coll : ℚ) / (N * odd128.card) ≤ 1 / 2 ^ 64 + 1 / 2 ^ 63 := by
  rw [card_odd128]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp only [Nat.cast_zero, zero_mul, div_zero]; positivity
  have h1 : c0 * 2 ^ 127 ≤ N * 2 ^ 63 := by
    calc c0 * 2 ^ 127 = c0 * 2 ^ 64 * 2 ^ 63 := by ring
      _ ≤ N * 2 ^ 63 := Nat.mul_le_mul_right _ hc0
  have h2 : coll ≤ N * 2 ^ 63 + N * 2 ^ 64 := hcoll.trans (Nat.add_le_add_right h1 _)
  rw [div_le_iff₀ (by positivity)]
  have e : ((1 : ℚ) / 2 ^ 64 + 1 / 2 ^ 63) * ((N : ℚ) * ((2 ^ 127 : ℕ) : ℚ)) =
      (N : ℚ) * 2 ^ 63 + N * 2 ^ 64 := by push_cast; ring
  rw [e]
  exact_mod_cast h2

/-! ### 主定理 -/

/-- **経路 A（L ≤ 32）の ε。** 違う 2 入力について Pr_{K, m}[衝突] ≤ 2⁻⁶⁴ + 2⁻⁶³。
fin と fmix64 は `hashA_eq_iff` により衝突を変えない。 -/
theorem pathA_eps (s s' : Bytes) (hs : s.length ≤ 32) (hs' : s'.length ≤ 32) (hne : s ≠ s') :
    (((univ ×ˢ odd128).filter fun p : KeyA × ℕ => preA p.1 p.2 s = preA p.1 p.2 s').card : ℚ) /
      (Fintype.card KeyA * odd128.card) ≤ 1 / 2 ^ 64 + 1 / 2 ^ 63 := by
  classical
  obtain ⟨j, ⟨a, a', ha, ha', hne'⟩, -⟩ := msgA_lastDiff hs hs' hne
  have hnh := nhO_eau (msgA s) (msgA s') j ha ha' hne'
  have hc := card_compose odd128 (fun K => accA K s) (fun K => accA K s') (ms 128 64) (2 ^ 64)
    fun K h => ms_stage (accA_lt K s) (accA_lt K s') h
  rw [card_odd128] at hc
  refine two_stage (c0 := (univ.filter fun K : KeyA => accA K s = accA K s').card) ?_ hc
  have e : (univ.filter fun K : KeyA => accA K s = accA K s') =
      univ.filter fun K => nhO K (msgA s) = nhO K (msgA s') :=
    Finset.filter_congr fun K _ => ⟨fun h => ZMod.val_injective _ h, fun h => by simp [accA, h]⟩
  rw [e, card_keys]
  exact hnh

/-- **経路 B（33 ≤ L ≤ 1024）の ε。** 違う 2 入力について Pr_{K, m}[衝突] ≤ 2⁻⁶⁴ + 2⁻⁶³。 -/
theorem pathB_eps (s s' : Bytes) (hs33 : 33 ≤ s.length) (hs : s.length ≤ 1024)
    (hs' : s'.length ≤ 1024) (hne : s ≠ s') :
    (((univ ×ˢ odd128).filter fun p : KeyB × ℕ => preB p.1 p.2 s = preB p.1 p.2 s').card : ℚ) /
      (Fintype.card KeyB * odd128.card) ≤ 1 / 2 ^ 64 + 1 / 2 ^ 63 := by
  classical
  obtain ⟨j, hj⟩ := msgB_lastDiff (by omega) hs hs' hne
  have hnh := nhT_eau (msgB s) (msgB s') j hj
  have hc := card_compose odd128 (fun K => accB K s) (fun K => accB K s') (ms 128 64) (2 ^ 64)
    fun K h => ms_stage (accB_lt K s) (accB_lt K s') h
  rw [card_odd128] at hc
  refine two_stage (c0 := (univ.filter fun K : KeyB => accB K s = accB K s').card) ?_ hc
  have e : (univ.filter fun K : KeyB => accB K s = accB K s') =
      univ.filter fun K => nhT K (msgB s) = nhT K (msgB s') :=
    Finset.filter_congr fun K _ => accB_eq_iff K s s'
  rw [e, card_keys]
  calc _ = (univ.filter fun K => nhT K (msgB s) = nhT K (msgB s')).card * ((2 : ℕ) ^ 32) ^ 2 := by
        norm_num
    _ ≤ _ := hnh

/-- 2⁻⁶⁴ + 2⁻⁶³ ≤ 2⁻⁶²（承認済みの目標「1KB 以下で 2⁻⁶²」）。 -/
theorem eps_le_target : (1 : ℚ) / 2 ^ 64 + 1 / 2 ^ 63 ≤ 1 / 2 ^ 62 := by norm_num

end LeanHash.Props
