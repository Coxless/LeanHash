/-
P3：核より外側。HashIR の核（`Kernels.lean`）を、Rust の `v2::hash_c`（スカラー版）と同じ形で組み合わせた参照実装。

| Rust（`rust/leanhash/src/v2.rs`） | ここ |
| :--- | :--- |
| `rd64` / `rd32`（`from_le_bytes`） | `rd64I` / `rd32I`（`rdLE`） |
| `nh_partial`（`hash` の L ≤ 32 の場合） | `nhPartialAI` |
| `hash`（L ≤ 32） | `hashAI` |
| `nh32x2_partial` のスカラーのループ | `nh32x2PartialI`（`laneLoop`） |
| `nh32x2_block_scalar` | `nh32x2FullI` |
| `hash_c` の 33..=1024 | `hashBI` |
| `hash_long_b` と `absorb` | `hashLongI` / `absorbI` |
| `hash_c` | `hashCI` |

仕様（`Props.hashV2c`）との一致は `LeanHash/Impl/OuterEquiv.lean` の `hashCI_eq`。
Rust との一致は差分テスト（`lake exe ref_vectors` の出力と `hash_c`、`rust/leanhash/src/v2.rs` の `lean_ref`）。

Rust との違い（どれも値は変わらない）:
- バイト列は `List (Fin 256)`、スライス `&data[a..b]` は `drop` / `take`
- レーンの和は 1 本の `foldl`（Rust のスカラー版は 8 本の部分和、AVX2 版は 4 レーンずつ。どれも mod 2⁶⁴ の和）
- `nh_partial` は L ≤ 32 で通る分岐だけ（`hash_c` は L ≤ 32 でしか `hash` を呼ばない）

Mathlib に依存しない（`lake exe ref_vectors` で実行するため）。
-/
import LeanHash.Impl.Kernels

namespace LeanHash.Impl

open LeanHash.IR

/-! ### 鍵（Rust の `v2::Keys`） -/

structure KeysI where
  /-- NH の鍵 130 語 -/
  nh : Fin 130 → BitVec 64
  /-- multiply-shift の乗数（奇数） -/
  m : BitVec 128
  /-- 多項式の評価点（p 未満） -/
  r : BitVec 64
  fin : BitVec 64
  finMid : BitVec 64
  finLong : BitVec 64

/-- `k[i]`（範囲外は 0。参照実装では範囲外を読まない）。 -/
def KeysI.k (K : KeysI) (i : Nat) : BitVec 64 := if h : i < 130 then K.nh ⟨i, h⟩ else 0

/-! ### 核の呼び出し（Rust の `kernel::*`） -/

def laneI (v k : BitVec 64) : BitVec 64 := nh32LaneK.run ((Env.empty.arg64 "v" v).arg64 "k" k)

def pairI (a b ka kb : BitVec 64) : BitVec 128 :=
  nhPairK.run ((((Env.empty.arg64 "a" a).arg64 "b" b).arg64 "ka" ka).arg64 "kb" kb)

def hornerI (h r c : BitVec 64) : BitVec 64 := hornerK.run (((Env.empty.arg64 "h" h).arg64 "r" r).arg64 "c" c)

def limb0I (x : BitVec 64) : BitVec 64 := limb0K.run (Env.empty.arg64 "x" x)
def limb1I (x y : BitVec 64) : BitVec 64 := limb1K.run ((Env.empty.arg64 "x" x).arg64 "y" y)
def limb2I (y : BitVec 64) : BitVec 64 := limb2K.run (Env.empty.arg64 "y" y)

def msI (m x : BitVec 128) : BitVec 64 := msK.run ((Env.empty.arg128 "m" m).arg128 "x" x)

def finishI (pre fin : BitVec 64) : BitVec 64 := finishK.run ((Env.empty.arg64 "pre" pre).arg64 "fin" fin)

/-! ### バイトの読み出し -/

/-- i バイト目（範囲外は 0）。 -/
def byteI (s : List (Fin 256)) (i : Nat) : Nat := (s.getD i 0).val

/-- o バイト目から k バイトを little-endian で読む。 -/
def rdLE (s : List (Fin 256)) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, o => byteI s o + 256 * rdLE s k (o + 1)

/-- Rust の `rd64(b, i)`。 -/
def rd64I (s : List (Fin 256)) (o : Nat) : BitVec 64 := BitVec.ofNat 64 (rdLE s 8 o)

/-- Rust の `rd32(b, i)`（u32 を読んで u64 に広げる）。 -/
def rd32I (s : List (Fin 256)) (o : Nat) : BitVec 64 := BitVec.ofNat 64 (rdLE s 4 o)

/-- `(y as u128) << 64 | x as u128`。 -/
def pack (x y : BitVec 64) : BitVec 128 := (y.setWidth 128 <<< 64) ||| x.setWidth 128

/-! ### 経路 A（L ≤ 32、NH64） -/

/-- `nh_partial`（L ≤ 32）。L ≤ 16 は 1 組（重なり読み）、17〜32 は前 16 バイトと末尾 16 バイトの 2 組。 -/
def nhPartialAI (K : KeysI) (b : List (Fin 256)) : BitVec 128 :=
  let len := b.length
  if len ≤ 16 then
    if len = 0 then 0
    else
      let xy : BitVec 64 × BitVec 64 :=
        if 8 ≤ len then (rd64I b 0, rd64I b (len - 8))
        else if 4 ≤ len then (rd32I b 0, rd32I b (len - 4))
        else (BitVec.ofNat 64 (byteI b 0) ||| BitVec.ofNat 64 (byteI b (len / 2)) <<< 8 |||
          BitVec.ofNat 64 (byteI b (len - 1)) <<< 16, 0)
      pairI xy.1 xy.2 (K.k 0) (K.k 1)
  else
    -- pairs = 2：本体の 32 バイト単位のループは回らず、端数の組 p = 0 と最後の組 q = 1
    pairI (rd64I b 0) (rd64I b 8) (K.k 0) (K.k 1) + pairI (rd64I b (len - 16)) (rd64I b (len - 8)) (K.k 2) (K.k 3)

/-- `hash`（L ≤ 32）：長さの組（鍵 128, 129）を足して multiply-shift → 仕上げ。 -/
def hashAI (K : KeysI) (b : List (Fin 256)) : BitVec 64 :=
  finishI (msI K.m (nhPartialAI K b + pairI (BitVec.ofNat 64 b.length) 0 (K.k 128) (K.k 129))) K.fin

/-! ### NH32×2（Toeplitz 2 本） -/

/-- レーン i = 0, …, n−1 の値を v i として、2 本の和（1 本目は鍵 i、2 本目は鍵 i+1）。 -/
def laneLoop (K : KeysI) (v : Nat → BitVec 64) (n : Nat) : BitVec 64 × BitVec 64 :=
  (List.range n).foldl (fun a i => (a.1 + laneI (v i) (K.k i), a.2 + laneI (v i) (K.k (i + 1)))) (0, 0)

/-- `nh32x2_partial`（8 ≤ L ≤ 1024）：レーン i は 8i バイト目から、最後のレーンは末尾 8 バイト（重ねて読む）。 -/
def nh32x2PartialI (K : KeysI) (b : List (Fin 256)) : BitVec 64 × BitVec 64 :=
  let len := b.length
  let lanes := (len + 7) / 8
  laneLoop K (fun i => if i + 1 = lanes then rd64I b (len - 8) else rd64I b (8 * i)) lanes

/-- `nh32x2_block_scalar`（1024 バイト）：128 レーン。 -/
def nh32x2FullI (K : KeysI) (b : List (Fin 256)) : BitVec 64 × BitVec 64 :=
  laneLoop K (fun i => rd64I b (8 * i)) 128

/-- 長さレーン（鍵の位置 128。Toeplitz の 2 本目は 129）を足す。 -/
def addLenI (K : KeysI) (xy : BitVec 64 × BitVec 64) (len : Nat) : BitVec 64 × BitVec 64 :=
  (xy.1 + laneI (BitVec.ofNat 64 len) (K.k 128), xy.2 + laneI (BitVec.ofNat 64 len) (K.k 129))

/-- `hash_c` の 33..=1024。 -/
def hashBI (K : KeysI) (b : List (Fin 256)) : BitVec 64 :=
  let xy := addLenI K (nh32x2PartialI K b) b.length
  finishI (msI K.m (pack xy.1 xy.2)) K.finMid

/-! ### 長い経路（L > 1024） -/

/-- `absorb`：NH32×2 の出力 (x, y) を 60bit limb 3 つにして Horner、t に y を足す。 -/
def absorbI (K : KeysI) (st : BitVec 64 × BitVec 64) (o : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  let h := hornerI st.1 K.r (limb0I o.1)
  let h := hornerI h K.r (limb1I o.1 o.2)
  let h := hornerI h K.r (limb2I o.2)
  (h, st.2 + o.2)

/-- 最後のブロックの NH32×2（端数があれば末尾 max(rem, 8) バイト）＋長さレーン。 -/
def lastBlockI (K : KeysI) (s : List (Fin 256)) : BitVec 64 × BitVec 64 :=
  let len := s.length
  let rem := len % 1024
  addLenI K (if 0 < rem then nh32x2PartialI K (s.drop (len - max rem 8)) else (0, 0)) len

/-- `hash_long_b`。 -/
def hashLongI (K : KeysI) (s : List (Fin 256)) : BitVec 64 :=
  let len := s.length
  let st := (List.range (len / 1024)).foldl
    (fun st j => absorbI K st (nh32x2FullI K ((s.drop (1024 * j)).take 1024))) (0, 0)
  let st := absorbI K st (lastBlockI K s)
  let h := hornerI st.1 K.r (BitVec.ofNat 64 len)
  finishI (msI K.m (pack st.2 h)) K.finLong

/-! ### 全体 -/

/-- `hash_c`。 -/
def hashCI (K : KeysI) (s : List (Fin 256)) : BitVec 64 :=
  if s.length ≤ 32 then hashAI K s
  else if s.length ≤ 1024 then hashBI K s
  else hashLongI K s

end LeanHash.Impl
