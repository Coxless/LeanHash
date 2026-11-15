/-
P3.5：Aeneas で Rust から抽出した外側のループ（`LeanHash/Aeneas/Leanhash.lean`、元は `rust/leanhash/src/outer.rs`）が、
仕様と一致を証明済みの参照実装（`LeanHash/Impl/Outer.lean`）と一致することの証明。

| Rust（抽出） | 仕様（Hoare 三つ組 `f ⦃ post ⦄`：失敗も発散もせず、結果が post をみたす） |
| :--- | :--- |
| `kernel::nh32_lane` | `laneI`（HashIR の核の意味論）と同じ値（`nh32_lane_spec`） |
| `outer::rd64` | `rd64I`（8 バイトの little-endian）と同じ値。添字は範囲内（`rd64_spec`） |
| `outer::nh32x2_lanes` のループ | `laneStep` の繰り返し（`lanes_loop_spec`、`nh32x2_lanes_spec`） |
| `outer::nh32x2_partial_scalar` | 参照実装 `nh32x2PartialI`（`nh32x2_partial_scalar_spec`）。さらに仕様の `nhT`（`nh32x2_partial_scalar_nhT`） |

前提は 8 ≤ L ≤ 1024（Rust の呼び出し側 `v2::hash_c` / `hash_long_b` が保つ範囲）。
証明は Aeneas の `step*` で関数呼び出しを進め、ループは `loop.spec_decr_nat`（不変条件：残りのレーンの `foldl` が目標と一致）。
-/
import LeanHash.Aeneas.Leanhash
import LeanHash.Impl.OuterEquiv

open Aeneas Aeneas.Std Result
open LeanHash.Impl LeanHash.IR

namespace LeanHash.AeneasProof

theorem laneI_eq (v k : BitVec 64) :
    laneI v k = ((v + k) &&& 0xffffffff#64) * (((v >>> 32) + (k >>> 32)) &&& 0xffffffff#64) := by
  simp only [laneI, nh32LaneK]
  ir_simp

@[step]
theorem nh32_lane_spec (v k : U64) :
    leanhash.kernel.nh32_lane v k ⦃ r => r.bv = laneI v.bv k.bv ⦄ := by
  unfold leanhash.kernel.nh32_lane
  step*
  rw [laneI_eq]
  simp [*]

theorem or_shift (a c N n : ℕ) (hN : N = 2 ^ n) (ha : a < N) : a ||| c * N = a + c * N := by
  subst hN
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm]

/-- 8 バイトを OR とシフトで組んだ値は、little-endian の和。 -/
theorem or8_toNat (c0 c1 c2 c3 c4 c5 c6 c7 : BitVec 8) :
    (c0.setWidth 64 ||| c1.setWidth 64 <<< 8 ||| c2.setWidth 64 <<< 16 ||| c3.setWidth 64 <<< 24 |||
      c4.setWidth 64 <<< 32 ||| c5.setWidth 64 <<< 40 ||| c6.setWidth 64 <<< 48 |||
      c7.setWidth 64 <<< 56).toNat =
      c0.toNat + 256 * (c1.toNat + 256 * (c2.toNat + 256 * (c3.toNat + 256 * (c4.toNat + 256 *
        (c5.toNat + 256 * (c6.toNat + 256 * c7.toNat)))))) := by
  have h0 := c0.isLt; have h1 := c1.isLt; have h2 := c2.isLt; have h3 := c3.isLt
  have h4 := c4.isLt; have h5 := c5.isLt; have h6 := c6.isLt; have h7 := c7.isLt
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  norm_num only at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  rw [or_shift _ _ 256 8 rfl (by omega), or_shift _ _ 65536 16 rfl (by omega),
    or_shift _ _ 16777216 24 rfl (by omega), or_shift _ _ 4294967296 32 rfl (by omega),
    or_shift _ _ 1099511627776 40 rfl (by omega), or_shift _ _ 281474976710656 48 rfl (by omega),
    or_shift _ _ 72057594037927936 56 rfl (by omega)]
  ring

/-- Rust のバイト列（`Slice U8`）を参照実装のバイト列に。 -/
def bytesOf (b : Slice U8) : List (Fin 256) := b.val.map fun x => ⟨x.val, x.bv.isLt⟩

theorem getD_bytesOf (l : List U8) (j : ℕ) (hj : j < l.length) :
    (((l.map fun x : U8 => (⟨x.val, x.bv.isLt⟩ : Fin 256)).getD j 0 : Fin 256) : ℕ) = (l[j]'hj).bv.toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

theorem rdLE8_lt (s : List (Fin 256)) (o : ℕ) : rdLE s 8 o < 2 ^ 64 := by
  rw [rdLE_eq]; exact LeanHash.Spec.readLE8_lt s o

@[step]
theorem rd64_spec (b : Slice U8) (i : Usize) (h : i.val + 8 ≤ b.length) :
    leanhash.outer.rd64 b i ⦃ r => r.bv = rd64I (bytesOf b) i.val ⦄ := by
  unfold leanhash.outer.rd64
  have h' : i.val + 8 ≤ b.val.length := h
  step*
  simp only [UScalar.bv_or, UScalar.cast_bv_eq, UScalarTy.numBits, *]
  simp (disch := omega) only [List.getElem_slice, Nat.add_zero]
  apply BitVec.eq_of_toNat_eq
  rw [or8_toNat]
  rw [rd64I, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rdLE8_lt _ _)]
  simp (disch := omega) only [rdLE, byteI, bytesOf, getD_bytesOf, Nat.add_assoc, Nat.reduceAdd, mul_zero,
    add_zero]

/-! ### ループ -/

/-- Rust の鍵 `[u64; 130]` を参照実装の鍵に（NH の鍵だけを使う。ほかの欄は 0）。 -/
def keysOfArr (k : Array U64 130#usize) : KeysI where
  nh j := (k.val[j.val]!).bv
  m := 0
  r := 0
  fin := 0
  finMid := 0
  finLong := 0

theorem keysOfArr_k (k : Array U64 130#usize) (j : ℕ) (hj : j < 130) :
    (keysOfArr k).k j = (k.val[j]!).bv := by
  simp [KeysI.k, keysOfArr, hj]

/-- `laneLoop` の 1 ステップ。 -/
def laneStep (K : KeysI) (v : ℕ → BitVec 64) (a : BitVec 64 × BitVec 64) (i : ℕ) : BitVec 64 × BitVec 64 :=
  (a.1 + laneI (v i) (K.k i), a.2 + laneI (v i) (K.k (i + 1)))

/-- 端数の読み方（参照実装 `nh32x2PartialI` のレーンの値）。 -/
def laneVal (bs : List (Fin 256)) (i : ℕ) : BitVec 64 :=
  if i + 1 = (bs.length + 7) / 8 then rd64I bs (bs.length - 8) else rd64I bs (8 * i)

theorem foldl_range'_succ {α : Type} (F : α → ℕ → α) (acc : α) {j n : ℕ} (h : j < n) :
    (List.range' j (n - j)).foldl F acc = (List.range' (j + 1) (n - (j + 1))).foldl F (F acc j) := by
  rw [show n - j = (n - (j + 1)) + 1 by omega, List.range'_succ, List.foldl_cons]

theorem length_bytesOf (b : Slice U8) : (bytesOf b).length = b.length := by
  simp [bytesOf, Slice.length]

/-- **ループの仕様。** レーン i..lanes−1 を足した結果は、参照実装の 1 ステップの繰り返し。 -/
theorem lanes_loop_spec (k : Array U64 130#usize) (b : Slice U8) (lanes len : Usize) (s1 s2 : U64)
    (i : Usize) (hlen : len.val = b.length) (h8 : 8 ≤ b.length) (h1024 : b.length ≤ 1024)
    (hl : lanes.val = (b.length + 7) / 8) (hi : i.val ≤ lanes.val) :
    leanhash.outer.nh32x2_lanes_loop k b lanes len s1 s2 i ⦃ r1 r2 =>
      (r1.bv, r2.bv) = (List.range' i.val (lanes.val - i.val)).foldl
        (laneStep (keysOfArr k) (laneVal (bytesOf b))) (s1.bv, s2.bv) ⦄ := by
  unfold leanhash.outer.nh32x2_lanes_loop
  apply loop.spec_decr_nat (fun x => lanes.val - x.2.2.val)
    (fun x => x.2.2.val ≤ lanes.val ∧
      (List.range' x.2.2.val (lanes.val - x.2.2.val)).foldl (laneStep (keysOfArr k) (laneVal (bytesOf b)))
        (x.1.bv, x.2.1.bv) =
      (List.range' i.val (lanes.val - i.val)).foldl (laneStep (keysOfArr k) (laneVal (bytesOf b))) (s1.bv, s2.bv))
  · rintro ⟨t1, t2, j⟩ ⟨hj, hinv⟩
    simp only at hj hinv ⊢
    unfold leanhash.outer.nh32x2_lanes_loop.body
    have hbs := length_bytesOf b
    have hlanes : lanes.val ≤ 128 := by omega
    split
    · rename_i hlt
      have hlt' : j.val < lanes.val := hlt
      step*
      split
      · rename_i heq
        have heq' : i1.val = lanes.val := by rw [heq]
        step*
        have hk : (keysOfArr k).k j.val = i2.bv := by
          rw [keysOfArr_k k _ (by omega), i2_post, getElem!_pos]
        have hk1 : (keysOfArr k).k (j.val + 1) = i4.bv := by
          have hk130 : j.val + 1 < k.val.length := by scalar_tac
          rw [keysOfArr_k k _ (by omega), i4_post, getElem!_pos k.val (j.val + 1) hk130]
          simp only [i1_post]
        have hv : laneVal (bytesOf b) j.val = v.bv := by
          rw [v_post, laneVal, hbs, ite_eq_left (by omega), x_post, hlen]
        refine ⟨by omega, ?_, by omega⟩
        rw [← hinv, foldl_range'_succ _ _ hlt', i1_post]
        simp only [laneStep, hk, hk1, hv, ← i3_post, ← i5_post, s11_post, s21_post,
          core.num.U64.wrapping_add_bv_eq]
      · rename_i hne
        have hne' : i1.val ≠ lanes.val := fun h => hne (UScalar.eq_of_val_eq h)
        step*
        have hk : (keysOfArr k).k j.val = i2.bv := by
          rw [keysOfArr_k k _ (by omega), i2_post, getElem!_pos]
        have hk1 : (keysOfArr k).k (j.val + 1) = i4.bv := by
          have hk130 : j.val + 1 < k.val.length := by scalar_tac
          rw [keysOfArr_k k _ (by omega), i4_post, getElem!_pos k.val (j.val + 1) hk130]
          simp only [i1_post]
        have hv : laneVal (bytesOf b) j.val = v.bv := by
          simp only [v_post, laneVal, hbs, x_post, show ¬ (j.val + 1 = (b.length + 7) / 8) by omega,
            ite_false]
        refine ⟨by omega, ?_, by omega⟩
        rw [← hinv, foldl_range'_succ _ _ hlt', i1_post]
        simp only [laneStep, hk, hk1, hv, ← i3_post, ← i5_post, s11_post, s21_post,
          core.num.U64.wrapping_add_bv_eq]
    · rename_i hge
      have hge' : ¬ j.val < lanes.val := hge
      have hjl : j.val = lanes.val := by omega
      simp only [WP.spec_ok, WP.uncurry'_pair]
      rw [← hinv]
      simp only [hjl, Nat.sub_self, List.range'_zero, List.foldl_nil]
  · exact ⟨hi, rfl⟩

/-- `nh32x2_lanes`（ループの開始位置 start から）。 -/
@[step]
theorem nh32x2_lanes_spec (k : Array U64 130#usize) (b : Slice U8) (lanes start : Usize) (s1 s2 : U64)
    (h8 : 8 ≤ b.length) (h1024 : b.length ≤ 1024) (hl : lanes.val = (b.length + 7) / 8)
    (hs : start.val ≤ lanes.val) :
    leanhash.outer.nh32x2_lanes k b lanes start s1 s2 ⦃ r1 r2 =>
      (r1.bv, r2.bv) = (List.range' start.val (lanes.val - start.val)).foldl
        (laneStep (keysOfArr k) (laneVal (bytesOf b))) (s1.bv, s2.bv) ⦄ := by
  unfold leanhash.outer.nh32x2_lanes
  exact lanes_loop_spec k b lanes _ s1 s2 start (by simp [Slice.length]) h8 h1024 hl hs

/-- **端数の NH32×2（Rust、スカラー版の全体）= 参照実装 `nh32x2PartialI`。** -/
@[step]
theorem nh32x2_partial_scalar_spec (k : Array U64 130#usize) (b : Slice U8) (h8 : 8 ≤ b.length)
    (h1024 : b.length ≤ 1024) :
    leanhash.outer.nh32x2_partial_scalar k b ⦃ r1 r2 =>
      (r1.bv, r2.bv) = nh32x2PartialI (keysOfArr k) (bytesOf b) ⦄ := by
  unfold leanhash.outer.nh32x2_partial_scalar
  step as ⟨n, hn⟩
  have hi1 : n.val = (b.length + 7) / 8 := by
    rw [hn, Nat.ceilDiv_eq_add_pred_div, Slice.len_val]; omega
  step as ⟨r1, r2, hr⟩
  rw [hr, hi1, Nat.sub_zero, ← List.range_eq_range', ← length_bytesOf]
  rfl

/-- **Rust（抽出）から仕様まで。** 端数（8 ≤ L ≤ 1024）の NH32×2 の Rust の出力に長さレーンを足したものは、
仕様の NH32×2 `nhT`（`msgB` で読んだレーン、Toeplitz 2 本）そのもの。
（参照実装を経由する: `nh32x2_partial_scalar_spec` と `Impl.partial_nhT`） -/
theorem nh32x2_partial_scalar_nhT (k : Array U64 130#usize) (b : Slice U8) (h8 : 8 ≤ b.length)
    (h1024 : b.length ≤ 1024) :
    leanhash.outer.nh32x2_partial_scalar k b ⦃ r1 r2 =>
      LeanHash.Props.nhT (LeanHash.Props.eB (wordsOf (keysOfArr k))) (LeanHash.Spec.msgB (bytesOf b)) =
        (z64 r1.bv + LeanHash.Props.termO (LeanHash.Spec.msgB (bytesOf b) (Fin.last 128))
            (lane32 ((keysOfArr k).k 128)),
          z64 r2.bv + LeanHash.Props.termO (LeanHash.Spec.msgB (bytesOf b) (Fin.last 128))
            (lane32 ((keysOfArr k).k 129))) ⦄ := by
  refine WP.spec_mono (nh32x2_partial_scalar_spec k b h8 h1024) ?_
  rintro ⟨r1, r2⟩ h
  simp only [WP.uncurry'_pair, Prod.ext_iff] at h ⊢
  rw [partial_nhT (keysOfArr k) (bytesOf b) (by rw [length_bytesOf]; exact h8)
    (by rw [length_bytesOf]; exact h1024) _ fun _ _ => rfl, h.1, h.2]
  exact ⟨rfl, rfl⟩

end LeanHash.AeneasProof
