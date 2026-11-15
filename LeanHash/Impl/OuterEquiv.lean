/-
P3：参照実装（`Outer.lean`）と仕様（`Props.hashV2c`）の一致。

主定理 `hashCI_eq`：鍵の r が p 未満、入力の長さが p 未満なら、`hashCI K s = hashV2c …`。
鍵の対応は `wordsOf`（u64 × 130 語をそのまま `Words` に）、m は `K.m.toNat`、r は `(K.r.toNat : ZMod p)`。

証明の流れ:
1. バイト読み：`rdLE = readLE`、8 バイト読みを 4 バイト 2 つに分ける（`readLE_add`）
2. レーンのループ：`laneLoop` の値（ZMod 2⁶⁴ に写したもの）は、レーンの積の和（`laneLoop_z`）
3. 仕様の NH（Fin 129 の和）を、範囲内のレーンだけの和と長さレーンに分ける（`nhT_split`）
4. 経路ごとに組み立てる（`hashAI_eq`、`hashBI_eq`、`hashLongI_eq`）
-/
import LeanHash.Impl.Outer
import LeanHash.Impl.Equiv
import LeanHash.Props.All

namespace LeanHash.Impl

open Finset LeanHash.IR LeanHash.Spec LeanHash.Props

/-! ### バイト読み -/

theorem byteI_eq (s : Bytes) (i : ℕ) : byteI s i = byteAt s i := rfl

theorem rdLE_eq (s : Bytes) (k o : ℕ) : rdLE s k o = readLE k s o := by
  induction k generalizing o with
  | zero => simp [rdLE, readLE]
  | succ k ih => rw [rdLE, readLE_succ, ih, byteI_eq]

theorem readLE_add (a b : ℕ) (s : Bytes) (o : ℕ) :
    readLE (a + b) s o = readLE a s o + 256 ^ a * readLE b s (o + a) := by
  induction a generalizing o with
  | zero => simp [readLE]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by ring, readLE_succ, readLE_succ, ih, pow_succ,
      show o + 1 + a = o + (a + 1) by ring]
    ring

theorem wd_mod (b n : ℕ) : wd b (n % 2 ^ b) = wd b n := Fin.ext (by simp [wd])

theorem wd_toNat_ofNat (b n : ℕ) : wd b (BitVec.ofNat b n).toNat = wd b n := by
  rw [BitVec.toNat_ofNat, wd_mod]

/-- 8 バイト読んだ u64 を NH32 のレーンと読むと、前 4 バイトと後ろ 4 バイト。 -/
theorem lane32_rd64 (s : Bytes) (o : ℕ) :
    lane32 (rd64I s o) = (wd 32 (readLE 4 s o), wd 32 (readLE 4 s (o + 4))) := by
  have e := readLE_add 4 4 s o
  have h1 := readLE4_lt s o
  have h2 := readLE4_lt s (o + 4)
  have h8 := readLE8_lt s o
  simp only [lane32, rd64I, rdLE_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h8]
  norm_num only at e h1 h2 ⊢
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp only [wd] <;> omega

/-! ### u64 / u128 を ZMod に写す -/

/-- u64 の値を NH32×2 の出力の型（ZMod (2³²)²）に。 -/
def z64 (a : BitVec 64) : ZMod ((2 ^ 32) ^ 2) := (a.toNat : ZMod ((2 ^ 32) ^ 2))

/-- u128 の値を NH64 の出力の型（ZMod (2⁶⁴)²）に。 -/
def z128 (a : BitVec 128) : ZMod ((2 ^ 64) ^ 2) := (a.toNat : ZMod ((2 ^ 64) ^ 2))

theorem z64_add (a b : BitVec 64) : z64 (a + b) = z64 a + z64 b := by
  unfold z64
  rw [BitVec.toNat_add, show (2 : ℕ) ^ 64 = (2 ^ 32) ^ 2 by norm_num, ZMod.natCast_mod]
  push_cast; rfl

theorem z64_zero : z64 0 = 0 := by simp [z64]

theorem z128_add (a b : BitVec 128) : z128 (a + b) = z128 a + z128 b := by
  unfold z128
  rw [BitVec.toNat_add, show (2 : ℕ) ^ 128 = (2 ^ 64) ^ 2 by norm_num, ZMod.natCast_mod]
  push_cast; rfl

theorem z128_zero : z128 0 = 0 := by simp [z128]

theorem z64_val (a : BitVec 64) : (z64 a).val = a.toNat := by
  unfold z64
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (a.isLt.trans_eq (by norm_num))

theorem z128_val (a : BitVec 128) : (z128 a).val = a.toNat := by
  unfold z128
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (a.isLt.trans_eq (by norm_num))

/-! ### 核の呼び出し -/

theorem laneI_z (v k : BitVec 64) : z64 (laneI v k) = (pairVal (lane32 v) (lane32 k) : ZMod _) := by
  unfold z64 laneI
  rw [nh32LaneK_eq]

theorem pairI_z (a b ka kb : BitVec 64) :
    z128 (pairI a b ka kb) =
      (pairVal (W := 2 ^ 64) (wd 64 a.toNat, wd 64 b.toNat) (wd 64 ka.toNat, wd 64 kb.toNat) : ZMod _) := by
  unfold z128 pairI
  rw [nhPairK_eq]

theorem finishI_eq (pre fin : BitVec 64) : finishI pre fin = out fin pre.toNat := finishK_eq pre fin

theorem msI_toNat (m x : BitVec 128) : (msI m x).toNat = ms 128 64 m.toNat x.toNat := msK_eq m x

theorem pack_toNat (x y : BitVec 64) : (pack x y).toNat = x.toNat + 2 ^ 64 * y.toNat := by
  unfold pack
  have hx := x.isLt
  have hy := y.isLt
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
    Nat.mod_eq_of_lt (a := y.toNat * 2 ^ 64) (by omega), Nat.mul_comm, 
    ← Nat.two_pow_add_eq_or_of_lt hx]
  ring

/-! ### レーンのループ -/

theorem laneLoop_z (K : KeysI) (v : ℕ → BitVec 64) (n : ℕ) :
    z64 (laneLoop K v n).1 = ∑ i ∈ range n, (pairVal (lane32 (v i)) (lane32 (K.k i)) : ZMod _) ∧
      z64 (laneLoop K v n).2 = ∑ i ∈ range n, (pairVal (lane32 (v i)) (lane32 (K.k (i + 1))) : ZMod _) := by
  induction n with
  | zero => simp [laneLoop, z64]
  | succ n ih =>
    simp only [laneLoop, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [z64_add, z64_add, ih.1, ih.2, laneI_z, laneI_z, Finset.sum_range_succ, Finset.sum_range_succ]
    exact ⟨rfl, rfl⟩

/-! ### 鍵の対応 -/

/-- 鍵 130 語をそのまま仕様の `Words` に。 -/
def wordsOf (K : KeysI) : Words := fun i => ⟨(K.nh i).toNat, (K.nh i).isLt⟩

theorem eB_wordsOf (K : KeysI) (j : Fin 130) : eB (wordsOf K) j = lane32 (K.k j.val) := by
  simp [eB, viewB, wordsOf, lane32, KeysI.k, j.isLt]

/-! ### 仕様の NH32×2 をレーンのループに -/

/-- 範囲内のレーン（i < n）はループの値、それ以外は 0 として、Fin 128 の和を `range n` の和に。 -/
theorem sum_lanes (K : KeysI) (M : Fin 129 → Option (Fin (2 ^ 32) × Fin (2 ^ 32))) (v : ℕ → BitVec 64)
    (n : ℕ) (hn : n ≤ 128) (hin : ∀ i : Fin 129, i.val < n → M i = some (lane32 (v i)))
    (hout : ∀ i : Fin 129, n ≤ i.val → i.val < 128 → M i = none)
    (d : ℕ) (f : Fin 128 → Fin 130) (hf : ∀ i, (f i).val = i.val + d) :
    ∑ i : Fin 128, termO (M i.castSucc) (eB (wordsOf K) (f i)) =
      ∑ i ∈ range n, (pairVal (lane32 (v i)) (lane32 (K.k (i + d))) : ZMod _) := by
  let g : ℕ → ZMod ((2 ^ 32) ^ 2) := fun j =>
    if j < n then (pairVal (lane32 (v j)) (lane32 (K.k (j + d))) : ZMod _) else 0
  calc _ = ∑ i : Fin 128, g i.val := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eB_wordsOf, hf]
        by_cases h : i.val < n
        · rw [hin i.castSucc (by simpa using h)]
          simp only [termO, g, h, ↓reduceIte, Fin.val_castSucc]
        · rw [hout i.castSucc (by simp; omega) (by simp)]
          simp only [termO, g, h, ↓reduceIte]
    _ = ∑ j ∈ range 128, g j := Fin.sum_univ_eq_sum_range g 128
    _ = _ := by
        simp only [g]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        omega

/-- **仕様の NH32×2 の分解。** レーン 0..n−1 がループの値、n..127 がなしなら、
`nhT` はループの値と位置 128 の項の和。 -/
theorem nhT_split (K : KeysI) (M : Fin 129 → Option (Fin (2 ^ 32) × Fin (2 ^ 32))) (v : ℕ → BitVec 64)
    (n : ℕ) (hn : n ≤ 128) (hin : ∀ i : Fin 129, i.val < n → M i = some (lane32 (v i)))
    (hout : ∀ i : Fin 129, n ≤ i.val → i.val < 128 → M i = none) :
    nhT (eB (wordsOf K)) M =
      (z64 (laneLoop K v n).1 + termO (M (Fin.last 128)) (lane32 (K.k 128)),
       z64 (laneLoop K v n).2 + termO (M (Fin.last 128)) (lane32 (K.k 129))) := by
  obtain ⟨h1, h2⟩ := laneLoop_z K v n
  rw [h1, h2]
  unfold nhT
  rw [Fin.sum_univ_castSucc (n := 128), Fin.sum_univ_castSucc (n := 128),
    sum_lanes K M v n hn hin hout 0 (fun i => i.castSucc.castSucc) (fun i => by simp),
    sum_lanes K M v n hn hin hout 1 (fun i => i.castSucc.succ) (fun i => by simp),
    eB_wordsOf, eB_wordsOf]
  rfl

/-! ### NH32×2 の端数・完全ブロック -/

theorem lane32_ofNat {L : ℕ} (h : L < 2 ^ 64) :
    lane32 (BitVec.ofNat 64 L) = (wd 32 L, wd 32 (L / 2 ^ 32)) := by
  simp only [lane32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- 端数（8 ≤ L ≤ 1024）：`nh32x2_partial` のループは、`msgB` の位置 128 以外の和。 -/
theorem partial_nhT (K : KeysI) (b : Bytes) (h8 : 8 ≤ b.length) (h1024 : b.length ≤ 1024)
    (M : Fin 129 → Option (Fin (2 ^ 32) × Fin (2 ^ 32))) (hM : ∀ i : Fin 129, i.val ≠ 128 → M i = msgB b i) :
    nhT (eB (wordsOf K)) M =
      (z64 (nh32x2PartialI K b).1 + termO (M (Fin.last 128)) (lane32 (K.k 128)),
       z64 (nh32x2PartialI K b).2 + termO (M (Fin.last 128)) (lane32 (K.k 129))) := by
  set L := b.length with hL
  refine nhT_split K M _ (lanesB L) (by unfold lanesB; omega) (fun i hi => ?_) (fun i hi hi' => ?_)
  · rw [hM i (by unfold lanesB at hi; omega)]
    unfold lanesB at hi
    simp only [msgB, lanesB, ← hL, show i.val ≠ 128 by omega, ↓reduceIte]
    split_ifs with h1 h2 h2
    · omega
    · rw [lane32_rd64]
    · rw [lane32_rd64, show L - 8 + 4 = L - 4 by omega]
    · omega
  · rw [hM i (by omega)]
    simp only [msgB, ← hL, show i.val ≠ 128 by omega, show ¬ (i.val + 1 < lanesB L) by omega,
      show i.val + 1 ≠ lanesB L by omega, ↓reduceIte]

/-- 完全ブロック（1024 バイト）：`nh32x2_block_scalar` は `msgB` の位置 128 以外の和。 -/
theorem full_nhT (K : KeysI) (b : Bytes) (hlen : b.length = 1024)
    (M : Fin 129 → Option (Fin (2 ^ 32) × Fin (2 ^ 32))) (hM : ∀ i : Fin 129, i.val ≠ 128 → M i = msgB b i) :
    nhT (eB (wordsOf K)) M =
      (z64 (nh32x2FullI K b).1 + termO (M (Fin.last 128)) (lane32 (K.k 128)),
       z64 (nh32x2FullI K b).2 + termO (M (Fin.last 128)) (lane32 (K.k 129))) := by
  refine nhT_split K M _ 128 le_rfl (fun i hi => ?_) (fun i hi hi' => by omega)
  rw [hM i (by omega)]
  have hl : lanesB b.length = 128 := by rw [hlen]; rfl
  simp only [msgB, hl, show i.val ≠ 128 by omega, ↓reduceIte]
  by_cases hlast : i.val + 1 = 128
  · simp only [hlast, lt_irrefl, ↓reduceIte, lane32_rd64, hlen, show 8 * i.val = 1016 by omega]
  · simp only [show i.val + 1 < 128 by omega, ↓reduceIte, lane32_rd64]

/-! ### 経路 B（33 ≤ L ≤ 1024） -/

theorem addLen_partial_z (K : KeysI) (b : Bytes) (h8 : 8 ≤ b.length) (h1024 : b.length ≤ 1024) :
    (z64 (addLenI K (nh32x2PartialI K b) b.length).1, z64 (addLenI K (nh32x2PartialI K b) b.length).2) =
      nhT (eB (wordsOf K)) (msgB b) := by
  rw [partial_nhT K b h8 h1024 (msgB b) fun _ _ => rfl]
  simp only [addLenI, z64_add, laneI_z, lane32_ofNat (show b.length < 2 ^ 64 by omega), msgB,
    Fin.val_last, ↓reduceIte, termO, Nat.div_eq_of_lt (show b.length < 2 ^ 32 by omega)]

theorem hashBI_eq (K : KeysI) (b : Bytes) (h8 : 8 ≤ b.length) (h1024 : b.length ≤ 1024) :
    hashBI K b = hashB (eB (wordsOf K)) K.m.toNat K.finMid b := by
  have hz := addLen_partial_z K b h8 h1024
  simp only [Prod.ext_iff] at hz
  unfold hashBI hashB preB accB
  rw [finishI_eq, msI_toNat, pack_toNat, ← hz.1, ← hz.2, z64_val, z64_val]

/-! ### 経路 A（L ≤ 32） -/

theorem eA_wordsOf (K : KeysI) (i : Fin 65) :
    eA (wordsOf K) i = (wd 64 (K.k (2 * i.val)).toNat, wd 64 (K.k (2 * i.val + 1)).toNat) := by
  have h1 : 2 * i.val < 130 := by omega
  have h2 : 2 * i.val + 1 < 130 := by omega
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;>
    simp [eA, viewA, wordsOf, KeysI.k, wd, h1, h2, Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- 1〜3 バイトの組み立て（OR とシフト）は足し算。 -/
theorem or3_toNat {a b c : ℕ} (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b <<< 8 ||| BitVec.ofNat 64 c <<< 16).toNat =
      a + 256 * b + 65536 * c := by
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega),
    Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (a := b * 2 ^ 8) (by omega),
    Nat.mod_eq_of_lt (a := c * 2 ^ 16) (by omega), Nat.mul_comm b, Nat.mul_comm c, Nat.or_comm a,
    ← Nat.two_pow_add_eq_or_of_lt (show a < 2 ^ 8 by omega), Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt (show 2 ^ 8 * b + a < 2 ^ 16 by omega)]
  ring

/-- 経路 A の組は 0, 1, 64 番だけ。 -/
theorem nhO_msgA (Ka : KeyA) (s : Bytes) :
    nhO Ka (msgA s) = termO (msgA s 0) (Ka 0) + termO (msgA s 1) (Ka 1) + termO (msgA s 64) (Ka 64) := by
  unfold nhO
  rw [← Finset.sum_subset (Finset.subset_univ ({0, 1, 64} : Finset (Fin 65))) fun i _ hi => ?_]
  · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have h0 : i.val ≠ 0 := fun h => hi.1 (Fin.ext h)
    have h1 : i.val ≠ 1 := fun h => hi.2.1 (Fin.ext h)
    have h64 : i.val ≠ 64 := fun h => hi.2.2 (Fin.ext h)
    simp only [msgA, h0, h1, h64, false_and, ↓reduceIte, termO]

/-- `nh_partial`（L ≤ 32）は組 0 と組 1 の和。 -/
theorem nhPartialAI_z (K : KeysI) (b : Bytes) (h32 : b.length ≤ 32) :
    z128 (nhPartialAI K b) =
      termO (msgA b 0) (eA (wordsOf K) 0) + termO (msgA b 1) (eA (wordsOf K) 1) := by
  rw [eA_wordsOf, eA_wordsOf]
  set L := b.length with hL
  unfold nhPartialAI
  by_cases h16 : L ≤ 16
  · have e1 : msgA b 1 = none := by simp [msgA, ← hL, show ¬ 16 < L by omega]
    rw [e1]
    simp only [← hL, h16, ↓reduceIte, termO, add_zero]
    by_cases hz : L = 0
    · simp [hz, msgA, ← hL, z128]
    · simp only [hz, ↓reduceIte, msgA, ← hL, h16, Fin.val_zero, show (0 : ℕ) ≠ 64 by omega, pairI_z]
      unfold shortPair
      by_cases h8 : 8 ≤ L
      · simp only [h8, ↓reduceIte, ← hL, rd64I, wd_toNat_ofNat, rdLE_eq]
      by_cases h4 : 4 ≤ L
      · simp only [h8, h4, ↓reduceIte, ← hL, rd32I, wd_toNat_ofNat, rdLE_eq]
      · simp only [h8, h4, ↓reduceIte, ← hL, byteI_eq]
        rw [or3_toNat (byteAt_lt _ _) (byteAt_lt _ _) (byteAt_lt _ _)]
        rfl
  · simp only [← hL, h16, ↓reduceIte, z128_add, pairI_z, msgA, Fin.val_zero, Fin.val_one,
      show (0 : ℕ) ≠ 64 by omega, show (1 : ℕ) ≠ 64 by omega, show L ≠ 0 by omega, show 16 < L by omega,
      and_self, termO, rd64I, wd_toNat_ofNat, rdLE_eq]
    rfl

/-- 長さの組（組 64）。 -/
theorem lenPairA_z (K : KeysI) (b : Bytes) :
    z128 (pairI (BitVec.ofNat 64 b.length) 0 (K.k 128) (K.k 129)) =
      termO (msgA b 64) (eA (wordsOf K) 64) := by
  rw [eA_wordsOf, pairI_z]
  simp only [msgA, termO, wd_toNat_ofNat]
  rfl

theorem hashAI_eq (K : KeysI) (b : Bytes) (h32 : b.length ≤ 32) :
    hashAI K b = hashA (eA (wordsOf K)) K.m.toNat K.fin b := by
  unfold hashAI hashA preA accA
  rw [finishI_eq, msI_toNat, ← z128_val (_ + _), z128_add, nhPartialAI_z K b h32, lenPairA_z K b,
    nhO_msgA]

/-! ### 長い経路（L > 1024）：ブロックごとの NH32×2 -/

/-- 完全ブロック j（j < ⌊L/1024⌋）。 -/
theorem fullBlock_z (K : KeysI) (s : Bytes) {j : ℕ} (hj : j < s.length / 1024) :
    (z64 (nh32x2FullI K ((s.drop (1024 * j)).take 1024)).1,
      z64 (nh32x2FullI K ((s.drop (1024 * j)).take 1024)).2) = outL (eB (wordsOf K)) s j := by
  unfold outL
  rw [full_nhT K (blk s j) (length_blk s hj) (msgL s j) fun i hi => by
    simp only [msgL, hj, ↓reduceIte, msgFull, hi]]
  simp only [msgL, hj, ↓reduceIte, msgFull, Fin.val_last, termO, add_zero]
  rfl

/-- 最後のブロック（端数＋長さレーン）。 -/
theorem lastBlock_z (K : KeysI) (s : Bytes) (h1024 : 1024 < s.length) (hL : s.length < 2 ^ 64) :
    (z64 (lastBlockI K s).1, z64 (lastBlockI K s).2) = outL (eB (wordsOf K)) s (s.length / 1024) := by
  set L := s.length with hLdef
  have hlast : msgL s (L / 1024) = msgLast s := by
    unfold msgL; rw [← hLdef, ite_eq_right_iff.mpr fun h => absurd h (lt_irrefl _)]
  unfold outL
  rw [hlast]
  unfold lastBlockI
  by_cases hrem : 0 < L % 1024
  · have ht := length_tail s (by omega)
    rw [partial_nhT K (tail s) (by rw [ht]; unfold tailLen; omega) (by rw [ht]; unfold tailLen; omega)
      (msgLast s) fun i hi => by simp only [msgLast, hi, ↓reduceIte, ← hLdef, show L % 1024 ≠ 0 by omega]]
    simp only [← hLdef, hrem, ↓reduceIte, addLenI, z64_add, laneI_z, lane32_ofNat hL, msgLast,
      Fin.val_last, termO, lenLane]
    rfl
  · rw [nhT_split K (msgLast s) (fun _ => 0) 0 (by omega) (fun i hi => by omega)
      fun i _ hi' => by simp only [msgLast, show i.val ≠ 128 by omega, ↓reduceIte, ← hLdef,
        show L % 1024 = 0 by omega]]
    simp only [← hLdef, hrem, ↓reduceIte, addLenI, z64_add, laneI_z, lane32_ofNat hL, msgLast,
      Fin.val_last, termO, lenLane]
    rfl

/-! ### 長い経路：absorb の繰り返し -/

/-- 参照実装の全ブロックの出力（完全ブロック、最後のブロック）。 -/
def outsI (K : KeysI) (s : Bytes) : List (BitVec 64 × BitVec 64) :=
  (List.range (s.length / 1024)).map (fun j => nh32x2FullI K ((s.drop (1024 * j)).take 1024)) ++
    [lastBlockI K s]

/-- 1 ブロックの limb 3 つ。 -/
def limbsI (o : BitVec 64 × BitVec 64) : List (BitVec 64) := [limb0I o.1, limb1I o.1 o.2, limb2I o.2]

/-- `absorb` の繰り返しは、limb の列への Horner と、y の和。 -/
theorem absorb_foldl (K : KeysI) (l : List (BitVec 64 × BitVec 64)) (st : BitVec 64 × BitVec 64) :
    l.foldl (absorbI K) st =
      ((l.flatMap limbsI).foldl (fun h c => hornerI h K.r c) st.1, st.2 + (l.map Prod.snd).sum) := by
  induction l generalizing st with
  | nil => simp
  | cons o l ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons, List.foldl_append, List.map_cons, List.sum_cons]
    simp only [absorbI, limbsI, List.foldl_cons, List.foldl_nil, BitVec.add_assoc]

theorem sum_toNat (l : List (BitVec 64)) : l.sum.toNat = (l.map BitVec.toNat).sum % 2 ^ 64 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons, BitVec.toNat_add, ih, List.map_cons, List.sum_cons]
    omega

theorem outsI_map (K : KeysI) (s : Bytes) (h1024 : 1024 < s.length) (hL : s.length < 2 ^ 64) :
    (outsI K s).map (fun o => (z64 o.1, z64 o.2)) = outs (eB (wordsOf K)) s := by
  unfold outsI outs nBlk
  rw [List.range_succ, List.map_append, List.map_append, List.map_map, List.map_singleton,
    List.map_singleton, lastBlock_z K s h1024 hL]
  refine congrArg (· ++ _) (List.map_congr_left fun j hj => ?_)
  rw [Function.comp_apply]
  exact fullBlock_z K s (List.mem_range.mp hj)

theorem limbsI_lt (o : BitVec 64 × BitVec 64) : ∀ c ∈ limbsI o, c.toNat < 2 ^ 63 := by
  have hx := o.1.isLt
  have hy := o.2.isLt
  intro c hc
  simp only [limbsI, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · rw [limb0I, limb0K_eq o.1 o.2]; omega
  · rw [limb1I, limb1K_eq]; omega
  · rw [limb2I, limb2K_eq o.1 o.2]
    have : o.1.toNat + 2 ^ 64 * o.2.toNat < 2 ^ 128 := by omega
    omega

theorem limbsI_map (o : BitVec 64 × BitVec 64) :
    (limbsI o).map (fun c => (c.toNat : ZMod P61)) = limbs (z64 o.1, z64 o.2) := by
  simp only [limbsI, limb0I, limb1I, limb2I]
  exact limbsK_eq o.1 o.2

theorem hashLongI_eq (K : KeysI) (hr : K.r.toNat < pNat) (s : Bytes) (h1024 : 1024 < s.length)
    (hL : s.length < P61) :
    hashLongI K s = hashL (eB (wordsOf K)) (K.r.toNat : ZMod P61) K.m.toNat K.finLong s := by
  have hL64 : s.length < 2 ^ 64 := lt_of_lt_of_le hL (by norm_num)
  -- 参照実装の状態を、全ブロックの出力に対する absorb の繰り返しに
  have hst : absorbI K ((List.range (s.length / 1024)).foldl
      (fun st j => absorbI K st (nh32x2FullI K ((s.drop (1024 * j)).take 1024))) (0, 0)) (lastBlockI K s) =
      (outsI K s).foldl (absorbI K) (0, 0) := by
    rw [outsI, List.foldl_append, List.foldl_map]; rfl
  unfold hashLongI hashL preL
  simp only
  rw [hst, absorb_foldl, finishI_eq, msI_toNat, pack_toNat]
  congr 2
  -- t
  have ht : ((0 : BitVec 64) + ((outsI K s).map Prod.snd).sum).toNat = tsum (eB (wordsOf K)) s := by
    rw [show ∀ x : BitVec 64, 0 + x = x from fun x => by simp, sum_toNat, Props.tsum, ← outsI_map K s h1024 hL64, List.map_map, List.map_map]
    congr 2
    refine List.map_congr_left fun o _ => ?_
    simp [z64_val]
  -- h
  have hh : (hornerI (((outsI K s).flatMap limbsI).foldl (fun h c => hornerI h K.r c) 0) K.r
      (BitVec.ofNat 64 s.length)).toNat = (polyH (eB (wordsOf K)) (K.r.toNat : ZMod P61) s).val := by
    have e : hornerI (((outsI K s).flatMap limbsI).foldl (fun h c => hornerI h K.r c) 0) K.r
        (BitVec.ofNat 64 s.length) = hornerRun K.r ((outsI K s).flatMap limbsI ++ [BitVec.ofNat 64 s.length]) := by
      change _ = List.foldl (fun h c => hornerI h K.r c) 0 (_ ++ _)
      rw [List.foldl_append]; rfl
    rw [e, hornerRun_eq hr]
    · unfold polyH coefs
      rw [List.map_append, List.map_flatMap, List.map_singleton, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hL64, ← outsI_map K s h1024 hL64, List.flatMap_map]
      simp only [limbsI_map]
    · intro c hc
      rw [List.mem_append, List.mem_flatMap, List.mem_singleton] at hc
      rcases hc with ⟨o, _, hco⟩ | rfl
      · exact limbsI_lt o c hco
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL64]
        exact lt_of_lt_of_le hL (by norm_num)
  rw [ht, hh]
  ring

/-! ### 全体 -/

/-- **参照実装 = 仕様。** 鍵の r が p 未満で、入力の長さが p = 2⁶¹ − 1 未満なら、
核を Rust の `hash_c` と同じ形で組み合わせた `hashCI` は `Props.hashV2c` と同じ値。 -/
theorem hashCI_eq (K : KeysI) (hr : K.r.toNat < pNat) (s : Bytes) (hL : s.length < P61) :
    hashCI K s = hashV2c (wordsOf K) K.m.toNat (K.fin, K.finMid) (K.r.toNat : ZMod P61) K.finLong s := by
  unfold hashCI hashV2c hash1K
  by_cases h32 : s.length ≤ 32
  · simp only [h32, ↓reduceIte, show s.length ≤ 1024 by omega]
    exact hashAI_eq K s h32
  by_cases h1024 : s.length ≤ 1024
  · simp only [h32, h1024, ↓reduceIte]
    exact hashBI_eq K s (by omega) h1024
  · simp only [h32, h1024, ↓reduceIte]
    exact hashLongI_eq K hr s (by omega) hL

/-! ### 参照実装の ε（鍵を一様に選んだときの衝突確率） -/

set_option linter.constructorNameAsVariable false

def keysEquiv : KeysI ≃ (Fin 130 → BitVec 64) × BitVec 128 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 where
  toFun K := (K.nh, K.m, K.r, K.fin, K.finMid, K.finLong)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- 鍵の全体（有限）。展開すると `Fin 130 → BitVec 64` の全列挙を whnf しようとして再帰が深くなりすぎるので、
既約にしておく（`Finset.mem_filter` を使うだけで maxRecDepth に達した）。 -/
@[irreducible] noncomputable def fintypeKeysI : Fintype KeysI := Fintype.ofEquiv _ keysEquiv.symm

attribute [instance] fintypeKeysI

/-- 正しい鍵：m は奇数、r は p 未満（Rust の `Keys::from_seed` が作る範囲）。 -/
noncomputable def validKeys : Finset KeysI := univ.filter fun K => K.m.toNat % 2 = 1 ∧ K.r.toNat < pNat

/-- 参照実装の鍵を仕様の鍵に。 -/
def keysOf (K : KeysI) : Keys :=
  ((((wordsOf K, K.m.toNat), (K.fin, K.finMid)), (K.r.toNat : ZMod P61)), K.finLong)

/-- 仕様の鍵を参照実装の鍵に（`keysOf` の逆）。 -/
def ofKeys (p : Keys) : KeysI where
  nh i := BitVec.ofNat 64 (p.1.1.1.1 i).val
  m := BitVec.ofNat 128 p.1.1.1.2
  r := BitVec.ofNat 64 p.1.2.val
  fin := p.1.1.2.1
  finMid := p.1.1.2.2
  finLong := p.2

/-! `p ∈ keySet` / `K ∈ validKeys` は `exact` で同じ型どうしを照合させるだけで maxRecDepth に達した
（`Fin.foldr.loop` を 540 回展開。鍵の全体集合を計算しようとしている）。どちらも `rw` で条件に書き換えてから使う。 -/

theorem mem_keySet_iff (p : Keys) : p ∈ keySet ↔ p.1.1.1.2 < 2 ^ 128 ∧ p.1.1.1.2 % 2 = 1 := by
  simp [keySet, odd128]

theorem mem_validKeys_iff (K : KeysI) : K ∈ validKeys ↔ K.m.toNat % 2 = 1 ∧ K.r.toNat < pNat := by
  simp [validKeys]

theorem ofKeys_keysOf {K : KeysI} (hK : K.r.toNat < pNat) : ofKeys (keysOf K) = K := by
  obtain ⟨nh, m, r, fin, finMid, finLong⟩ := K
  simp only [ofKeys, keysOf, wordsOf, BitVec.ofNat_toNat, BitVec.setWidth_eq, ZMod.val_natCast,
    Nat.mod_eq_of_lt (show r.toNat < P61 from hK)]

theorem keysOf_ofKeys {p : Keys} (hp : p.1.1.1.2 < 2 ^ 128) : keysOf (ofKeys p) = p := by
  obtain ⟨⟨⟨⟨w, m⟩, F⟩, r⟩, fl⟩ := p
  have hr : r.val < 2 ^ 64 := lt_of_lt_of_le (ZMod.val_lt r) (by norm_num)
  simp only [keysOf, ofKeys, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show m < 2 ^ 128 from hp),
    Nat.mod_eq_of_lt hr, ZMod.natCast_zmod_val, Prod.mk.eta]
  congr
  funext i
  exact Fin.ext (Nat.mod_eq_of_lt (w i).isLt)

/-- 正しい鍵の上の数え上げは、仕様の鍵の上の数え上げと同じ。 -/
theorem card_validKeys_filter (Q : Keys → Prop) [DecidablePred Q] :
    (validKeys.filter fun K => Q (keysOf K)).card = (keySet.filter Q).card := by
  refine Finset.card_bij' (fun K _ => keysOf K) (fun p _ => ofKeys p) (fun K hK => ?_) (fun p hp => ?_)
    (fun K hK => ?_) (fun p hp => ?_)
  · rw [Finset.mem_filter, mem_validKeys_iff] at hK
    rw [Finset.mem_filter, mem_keySet_iff]
    exact ⟨⟨K.m.isLt, hK.1.1⟩, hK.2⟩
  · rw [Finset.mem_filter, mem_keySet_iff] at hp
    rw [Finset.mem_filter, mem_validKeys_iff, keysOf_ofKeys hp.1.1]
    refine ⟨⟨?_, ?_⟩, hp.2⟩
    · simp only [ofKeys, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp.1.1, hp.1.2]
    · have hr := ZMod.val_lt p.1.2
      simp only [ofKeys, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show p.1.2.val < 2 ^ 64 from lt_of_lt_of_le hr (by norm_num))]
      exact hr
  · rw [Finset.mem_filter, mem_validKeys_iff] at hK
    exact ofKeys_keysOf hK.1.2
  · rw [Finset.mem_filter, mem_keySet_iff] at hp
    exact keysOf_ofKeys hp.1.1

/-- **参照実装の ε。** 違う 2 入力（長さ < p）について、正しい鍵（m は奇数、r < p、ほかは任意）を一様に選ぶと
Pr[`hashCI` が衝突] ≤ 2⁻⁶³ + (3N+1)/p（N = max(⌊L/1024⌋ + 1, ⌊L'/1024⌋ + 1)）。 -/
theorem hashCI_eps (s s' : Bytes) (hL : s.length < P61) (hL' : s'.length < P61) (hne : s ≠ s') :
    ((validKeys.filter fun K => hashCI K s = hashCI K s').card : ℚ) / validKeys.card ≤
      1 / 2 ^ 63 + (3 * max (nBlk s.length) (nBlk s'.length) + 1 : ℕ) / P61 := by
  let Q : Keys → Prop := fun p => hashV2c p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 s =
    hashV2c p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 s'
  have e1 : (validKeys.filter fun K => hashCI K s = hashCI K s') = validKeys.filter fun K => Q (keysOf K) := by
    refine Finset.filter_congr fun K hK => ?_
    rw [mem_validKeys_iff] at hK
    rw [hashCI_eq K hK.2 s hL, hashCI_eq K hK.2 s' hL']
    rfl
  have e2 : validKeys.card = keySet.card := by
    have := card_validKeys_filter (fun _ => True)
    rwa [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.filter_true_of_mem (fun _ _ => trivial)] at this
  rw [e1, card_validKeys_filter Q, e2, card_keySet]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact v2c_eps s s' hL hL' hne

end LeanHash.Impl
