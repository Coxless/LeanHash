/-
P3：HashIR の核と仕様の一致（`eval fast = spec`）。

| 核 | 一致する仕様 |
| :--- | :--- |
| `fmix64` | `Spec.fmix64` |
| `finish` | `Props.out`（fmix64(pre ^ fin)） |
| `nh32_lane` | `Spec.pairVal`（W = 2³²、u64 を (下位 32bit, 上位 32bit) の組と読む） |
| `nh_pair` | `Spec.pairVal`（W = 2⁶⁴） |
| `reduce` | x mod p（すべての u64） |
| `mulmod` | a·b mod p（a, b < p）= ZMod p の積 |
| `horner` | h·r + c mod p（h, r < p、c < 2⁶³）= ZMod p の h·r + c。繰り返すと `Props.horner` |
| `ms` | `Props.ms 128 64` |
| `limb0..2` | `Props.limbs` |

証明の方針（CLAUDE.md）: 乗算は `bv_decide` に渡さない。BitVec を `toNat` に落とし、積は 1 つの自然数として
上界だけを使い、あとは `omega`（mod / div は定数で割るものだけ）で閉じる。
同じ部分式を何度も読む文の並び（`reduce` など）は、先に「文の並び → 名前付きの BitVec 関数」の補題にしてから使う
（そのまま展開すると部分式が複製されて式が爆発した）。
-/
import LeanHash.Impl.Kernels
import LeanHash.Props.Long

namespace LeanHash.Impl

open LeanHash.IR LeanHash.Spec LeanHash.Props

/-! ### 意味論を開くための補題 -/

/-- 自然数の AND マスクは mod。 -/
theorem nat_and_mask (x n : ℕ) : x &&& (2 ^ n - 1) = x % 2 ^ n := Nat.and_two_pow_sub_one_eq_mod x n

theorem land_m61 (x : ℕ) : x &&& 2305843009213693951 = x % 2305843009213693952 := nat_and_mask x 61
theorem land_m60 (x : ℕ) : x &&& 1152921504606846975 = x % 1152921504606846976 := nat_and_mask x 60
theorem land_m32 (x : ℕ) : x &&& 4294967295 = x % 4294967296 := nat_and_mask x 32

/-- 意味論を開く simp 集合。 -/
macro "ir_simp" : tactic => `(tactic| simp only [Kernel.run, Stmt.exec, Expr.eval, Env.arg64, Env.arg128,
  Env.get_set_same, Env.get_set_ne, Env.get_set_other, ne_eq, String.reduceEq, String.reduceAppend, not_false_eq_true,
  reduceCtorEq, Ty.bin, Ty.shl, Ty.shr, Ty.lit, BinOp.eval, Expr.add_def, Expr.sub_def, Expr.mul_def,
  Expr.xor_def, Expr.and_def, Expr.or_def, Expr.shl_def, Expr.shr_def, Expr.v64_def, Expr.v128_def,
  Expr.k64_def, Expr.k128_def, List.foldl_cons, List.foldl_nil, List.foldl_append])

/-! ### fmix64 と仕上げ -/

theorem fmix64K_eq (x : BitVec 64) : fmix64K.run (Env.empty.arg64 "x" x) = fmix64 x := by
  simp only [fmix64K]
  ir_simp
  rfl

theorem finishK_eq (pre fin : BitVec 64) :
    finishK.run ((Env.empty.arg64 "pre" pre).arg64 "fin" fin) = out fin pre.toNat := by
  simp only [finishK, fmix64K]
  ir_simp
  simp only [out, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-! ### NH のレーンと組 -/

/-- u64 を NH32 の組（下位 32bit, 上位 32bit）と読む（`Props.viewB` と同じ読み方）。 -/
def lane32 (v : BitVec 64) : Fin (2 ^ 32) × Fin (2 ^ 32) := (wd 32 v.toNat, wd 32 (v.toNat / 2 ^ 32))

theorem nh32LaneK_eq (v k : BitVec 64) :
    (nh32LaneK.run ((Env.empty.arg64 "v" v).arg64 "k" k)).toNat = pairVal (lane32 v) (lane32 k) := by
  simp only [nh32LaneK]
  ir_simp
  have hv := v.isLt
  have hk := k.isLt
  simp only [BitVec.toNat_mul, BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, pairVal, lane32, wd, Fin.val_add]
  norm_num only
  simp only [land_m32]
  have e1 : (v.toNat + k.toNat) % 2 ^ 64 % 2 ^ 32 = (v.toNat % 2 ^ 32 + k.toNat % 2 ^ 32) % 2 ^ 32 := by
    omega
  have e2 : (v.toNat / 2 ^ 32 + k.toNat / 2 ^ 32) % 2 ^ 64 % 2 ^ 32 =
      (v.toNat / 2 ^ 32 % 2 ^ 32 + k.toNat / 2 ^ 32 % 2 ^ 32) % 2 ^ 32 := by omega
  norm_num only at e1 e2 ⊢
  rw [e1, e2]
  apply Nat.mod_eq_of_lt
  have := Nat.mul_lt_mul'' (Nat.mod_lt (v.toNat % 4294967296 + k.toNat % 4294967296) (by norm_num : 0 < 4294967296))
    (Nat.mod_lt (v.toNat / 4294967296 % 4294967296 + k.toNat / 4294967296 % 4294967296) (by norm_num : 0 < 4294967296))
  omega

theorem nhPairK_eq (a b ka kb : BitVec 64) :
    (nhPairK.run ((((Env.empty.arg64 "a" a).arg64 "b" b).arg64 "ka" ka).arg64 "kb" kb)).toNat =
      pairVal (W := 2 ^ 64) (wd 64 a.toNat, wd 64 b.toNat) (wd 64 ka.toNat, wd 64 kb.toNat) := by
  simp only [nhPairK]
  ir_simp
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_add, pairVal, wd, Fin.val_add]
  have ha := a.isLt; have hb := b.isLt; have hka := ka.isLt; have hkb := kb.isLt
  have e1 : (a.toNat + ka.toNat) % 2 ^ 64 % 2 ^ 128 = (a.toNat % 2 ^ 64 + ka.toNat % 2 ^ 64) % 2 ^ 64 := by
    omega
  have e2 : (b.toNat + kb.toNat) % 2 ^ 64 % 2 ^ 128 = (b.toNat % 2 ^ 64 + kb.toNat % 2 ^ 64) % 2 ^ 64 := by
    omega
  rw [e1, e2]
  apply Nat.mod_eq_of_lt
  have := Nat.mul_lt_mul'' (Nat.mod_lt (a.toNat % 2 ^ 64 + ka.toNat % 2 ^ 64) (by norm_num : 0 < 2 ^ 64))
    (Nat.mod_lt (b.toNat % 2 ^ 64 + kb.toNat % 2 ^ 64) (by norm_num : 0 < 2 ^ 64))
  calc _ < 2 ^ 64 * 2 ^ 64 := this
    _ = 2 ^ 128 := by norm_num

/-! ### mod p（reduce / mulmod / horner） -/

/-- `reduce` の y = (x mod 2⁶¹) + ⌊x/2⁶¹⌋。 -/
def yBV (x : BitVec 64) : BitVec 64 := (x &&& BitVec.ofNat 64 pNat) + (x >>> 61)

/-- `reduce`：y < p なら y、そうでなければ y − p。 -/
def redBV (x : BitVec 64) : BitVec 64 :=
  if (yBV x).toNat < pNat then yBV x else yBV x - BitVec.ofNat 64 pNat

/-- `mulmod` の前半：t = a·b（128bit）の (t mod 2⁶¹) + ⌊t/2⁶¹⌋。 -/
def sBV (a b : BitVec 64) : BitVec 64 :=
  (((a.setWidth 128 * b.setWidth 128).setWidth 64) &&& BitVec.ofNat 64 pNat) +
    ((a.setWidth 128 * b.setWidth 128) >>> 61).setWidth 64

theorem exec_reduceStmts (pre : String) (x : Expr .u64) (e : Env) :
    (reduceStmts pre x).foldl Stmt.exec e =
      (e.set .u64 (pre ++ "_y") (yBV (x.eval e))).set .u64 pre (redBV (x.eval e)) := by
  simp only [reduceStmts]
  ir_simp
  rfl

theorem exec_mulmodStmts (pre : String) (a b : Expr .u64) (e : Env) :
    (mulmodStmts pre a b).foldl Stmt.exec e =
      let e1 := (e.set .u128 (pre ++ "_t") ((a.eval e).setWidth 128 * (b.eval e).setWidth 128)).set .u64
        (pre ++ "_s") (sBV (a.eval e) (b.eval e))
      (e1.set .u64 (pre ++ "_y") (yBV (sBV (a.eval e) (b.eval e)))).set .u64 pre
        (redBV (sBV (a.eval e) (b.eval e))) := by
  simp only [mulmodStmts, List.foldl_cons, exec_reduceStmts]
  ir_simp
  rfl

theorem pNat_eq : pNat = 2 ^ 61 - 1 := rfl

theorem yBV_toNat (x : BitVec 64) : (yBV x).toNat = x.toNat % 2 ^ 61 + x.toNat / 2 ^ 61 := by
  have hx := x.isLt
  unfold yBV
  simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, pNat_eq]
  norm_num only at hx ⊢
  simp only [land_m61]
  omega

theorem redBV_toNat (x : BitVec 64) : (redBV x).toNat = x.toNat % pNat := by
  have hx := x.isLt
  have hy := yBV_toNat x
  unfold redBV
  by_cases h : (yBV x).toNat < pNat
  · simp only [h, ↓reduceIte]
    rw [hy]
    rw [hy, pNat_eq] at h
    rw [pNat_eq]
    omega
  · simp only [h, ↓reduceIte]
    rw [BitVec.toNat_sub, hy, BitVec.toNat_ofNat]
    rw [hy, pNat_eq] at h
    rw [pNat_eq]
    norm_num only at hx h ⊢
    omega

theorem sBV_toNat {a b : BitVec 64} (ha : a.toNat < pNat) (hb : b.toNat < pNat) :
    (sBV a b).toNat = a.toNat * b.toNat % 2 ^ 61 + a.toNat * b.toNat / 2 ^ 61 := by
  have hab : a.toNat * b.toNat < 2 ^ 122 := by
    calc _ < 2 ^ 61 * 2 ^ 61 := Nat.mul_lt_mul'' (ha.trans_le (by simp [pNat])) (hb.trans_le (by simp [pNat]))
      _ = _ := by norm_num
  unfold sBV
  simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_mul,
    BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, pNat_eq]
  have ha' := a.isLt; have hb' := b.isLt
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega)]
  generalize a.toNat * b.toNat = t at hab ⊢
  norm_num only at hab ⊢
  simp only [land_m61]
  omega

/-- `reduce` は全 u64 で x mod p。 -/
theorem reduceK_eq (x : BitVec 64) : (reduceK.run (Env.empty.arg64 "x" x)).toNat = x.toNat % pNat := by
  simp only [reduceK, Kernel.run, exec_reduceStmts]
  ir_simp
  exact redBV_toNat _

/-- `mulmod` は a, b < p で a·b mod p。 -/
theorem mulmodK_eq {a b : BitVec 64} (ha : a.toNat < pNat) (hb : b.toNat < pNat) :
    (mulmodK.run ((Env.empty.arg64 "a" a).arg64 "b" b)).toNat = a.toNat * b.toNat % pNat := by
  simp only [mulmodK, Kernel.run, exec_mulmodStmts]
  ir_simp
  rw [redBV_toNat, sBV_toNat ha hb, pNat_eq]
  omega

theorem P61_eq_pNat : P61 = pNat := rfl

/-- **Horner の 1 ステップ。** h, r < p、c < 2⁶³ なら、値は ZMod p の h·r + c。 -/
theorem hornerK_eq {h r c : BitVec 64} (hh : h.toNat < pNat) (hr : r.toNat < pNat)
    (hc : c.toNat < 2 ^ 63) :
    (hornerK.run (((Env.empty.arg64 "h" h).arg64 "r" r).arg64 "c" c)).toNat =
      ((h.toNat : ZMod P61) * r.toNat + c.toNat).val := by
  simp only [hornerK, Kernel.run, List.foldl_append, exec_mulmodStmts, exec_reduceStmts]
  ir_simp
  rw [redBV_toNat, BitVec.toNat_add, redBV_toNat, sBV_toNat hh hr]
  rw [show ((h.toNat : ZMod P61) * r.toNat + c.toNat) = ((h.toNat * r.toNat + c.toNat : ℕ) : ZMod P61) by
    push_cast; ring, ZMod.val_natCast, P61_eq_pNat, pNat_eq]
  have hhr : h.toNat * r.toNat < 2 ^ 122 := by
    calc _ < 2 ^ 61 * 2 ^ 61 := Nat.mul_lt_mul'' (hh.trans_le (by simp [pNat])) (hr.trans_le (by simp [pNat]))
      _ = _ := by norm_num
  generalize h.toNat * r.toNat = t at hhr ⊢
  omega

/-- `horner` の値は p 未満（繰り返しの不変条件）。 -/
theorem hornerK_lt {h r c : BitVec 64} (hh : h.toNat < pNat) (hr : r.toNat < pNat) (hc : c.toNat < 2 ^ 63) :
    (hornerK.run (((Env.empty.arg64 "h" h).arg64 "r" r).arg64 "c" c)).toNat < pNat := by
  rw [hornerK_eq hh hr hc]
  exact ZMod.val_lt _

/-- `horner` を係数列に繰り返し適用する（Rust の `absorb` の連鎖と、最後の長さ係数）。 -/
def hornerRun (r : BitVec 64) (cs : List (BitVec 64)) : BitVec 64 :=
  cs.foldl (fun h c => hornerK.run (((Env.empty.arg64 "h" h).arg64 "r" r).arg64 "c" c)) 0

/-- **ループへの持ち上げ。** 係数がどれも 2⁶³ 未満なら、`horner` の繰り返しは ZMod p の Horner（`Props.horner`）。 -/
theorem hornerRun_eq {r : BitVec 64} (hr : r.toNat < pNat) (cs : List (BitVec 64))
    (hcs : ∀ c ∈ cs, c.toNat < 2 ^ 63) :
    (hornerRun r cs).toNat = (Props.horner (r.toNat : ZMod P61) (cs.map fun c => (c.toNat : ZMod P61))).val := by
  unfold hornerRun Props.horner
  suffices ∀ (h : BitVec 64) (z : ZMod P61), h.toNat = z.val →
      (cs.foldl (fun h c => hornerK.run (((Env.empty.arg64 "h" h).arg64 "r" r).arg64 "c" c)) h).toNat =
        ((cs.map fun c => (c.toNat : ZMod P61)).foldl (fun h c => h * (r.toNat : ZMod P61) + c) z).val by
    exact this 0 0 (by simp)
  induction cs with
  | nil => intro h z e; simp only [List.foldl_nil, List.map_nil]; exact e
  | cons c cs ih =>
    intro h z e
    simp only [List.foldl_cons, List.map_cons]
    have hh : h.toNat < pNat := e ▸ ZMod.val_lt z
    have hc := hcs c (by simp)
    apply ih (fun c' hc' => hcs c' (by simp [hc']))
    rw [hornerK_eq hh hr hc, e, ZMod.natCast_val, ZMod.cast_id', id, mul_comm]

/-! ### multiply-shift と limb -/

theorem msK_eq (m x : BitVec 128) :
    (msK.run ((Env.empty.arg128 "m" m).arg128 "x" x)).toNat = Props.ms 128 64 m.toNat x.toNat := by
  simp only [msK]
  ir_simp
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    Nat.shiftRight_eq_div_pow, Props.ms]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt (m.toNat * x.toNat) (by norm_num : 0 < 2 ^ 128)
  rw [Nat.div_lt_iff_lt_mul (by norm_num)]
  calc _ < 2 ^ 128 := this
    _ = _ := by norm_num

theorem limb0K_eq (x y : BitVec 64) :
    (limb0K.run (Env.empty.arg64 "x" x)).toNat = (x.toNat + 2 ^ 64 * y.toNat) % 2 ^ 60 := by
  simp only [limb0K]
  ir_simp
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, mask60]
  norm_num only
  simp only [land_m60]
  omega

theorem limb1K_eq (x y : BitVec 64) :
    (limb1K.run ((Env.empty.arg64 "x" x).arg64 "y" y)).toNat =
      (x.toNat + 2 ^ 64 * y.toNat) / 2 ^ 60 % 2 ^ 60 := by
  simp only [limb1K]
  ir_simp
  have hx := x.isLt
  simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, mask60]
  norm_num only
  simp only [land_m60]
  -- x / 2⁶⁰ < 2⁴ と (y·2⁴ mod 2⁶⁴) の下位 4bit は 0 なので OR は足し算
  have hlt : x.toNat / 1152921504606846976 < 2 ^ 4 := by omega
  rw [show y.toNat * 16 % 18446744073709551616 = 2 ^ 4 * (y.toNat % 2 ^ 60) by omega,
    Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hlt, Nat.mul_comm]
  omega

theorem limb2K_eq (x y : BitVec 64) :
    (limb2K.run (Env.empty.arg64 "y" y)).toNat = (x.toNat + 2 ^ 64 * y.toNat) / 2 ^ 120 := by
  simp only [limb2K]
  ir_simp
  have hx := x.isLt
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- **limb の 3 核は `Props.limbs`。** (x, y) を NH32×2 の出力（ZMod (2³²)²）として読んだもの。 -/
theorem limbsK_eq (x y : BitVec 64) :
    [((limb0K.run (Env.empty.arg64 "x" x)).toNat : ZMod P61),
     ((limb1K.run ((Env.empty.arg64 "x" x).arg64 "y" y)).toNat : ZMod P61),
     ((limb2K.run (Env.empty.arg64 "y" y)).toNat : ZMod P61)] =
      limbs ((x.toNat : ZMod ((2 ^ 32) ^ 2)), (y.toNat : ZMod ((2 ^ 32) ^ 2))) := by
  have hx : (x.toNat : ZMod ((2 ^ 32) ^ 2)).val = x.toNat := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (x.isLt.trans_eq (by norm_num))
  have hy : (y.toNat : ZMod ((2 ^ 32) ^ 2)).val = y.toNat := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (y.isLt.trans_eq (by norm_num))
  simp only [limbs, hx, hy, limb0K_eq x y, limb1K_eq x y, limb2K_eq x y]

end LeanHash.Impl
