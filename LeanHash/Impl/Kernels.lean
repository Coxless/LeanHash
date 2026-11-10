/-
P3：HashIR で書いた計算の核。`rust/leanhash/src/kernel.rs` はここから出力する（`lake exe emit_rust`）。

どれも手書き試作（`rust/leanhash/src/lib.rs` / `v2.rs`）の同名の関数と同じ計算を、同じ順序で書いたもの。
仕様との一致は `LeanHash/Impl/Equiv.lean`。
-/
import LeanHash.IR.Semantics

namespace LeanHash.Impl

open LeanHash.IR LeanHash.IR.Expr

/-- p = 2⁶¹ − 1。 -/
def pNat : Nat := 2 ^ 61 - 1

/-- `reduce` の本体（x → x mod p、x < 2⁶⁴ で y < 2p のとき）を、名前 `pre` を付けた文の並びにする。 -/
def reduceStmts (pre : String) (x : Expr .u64) : List Stmt :=
  [⟨.u64, pre ++ "_y", (x &&& k64 pNat) + (x >>> 61)⟩,
   ⟨.u64, pre, iteLt (v64 (pre ++ "_y")) (k64 pNat) (v64 (pre ++ "_y")) (v64 (pre ++ "_y") - k64 pNat)⟩]

/-- `mulmod` の本体（a·b mod p、a, b < p）。 -/
def mulmodStmts (pre : String) (a b : Expr .u64) : List Stmt :=
  ⟨.u128, pre ++ "_t", ext a * ext b⟩ ::
  ⟨.u64, pre ++ "_s", (trunc (v128 (pre ++ "_t")) &&& k64 pNat) + trunc (v128 (pre ++ "_t") >>> 61)⟩ ::
  reduceStmts pre (v64 (pre ++ "_s"))

/-- MurmurHash3 の fmix64。 -/
def fmix64K : Kernel where
  name := "fmix64"
  doc := "MurmurHash3 の fmix64（全単射）。"
  params := [("x", .u64)]
  body := [
    ⟨.u64, "x1", v64 "x" ^^^ (v64 "x" >>> 33)⟩,
    ⟨.u64, "x2", v64 "x1" * k64 0xff51afd7ed558ccd⟩,
    ⟨.u64, "x3", v64 "x2" ^^^ (v64 "x2" >>> 33)⟩,
    ⟨.u64, "x4", v64 "x3" * k64 0xc4ceb9fe1a85ec53⟩]
  retTy := .u64
  ret := v64 "x4" ^^^ (v64 "x4" >>> 33)

/-- NH32 の 1 レーン：(lo(v)+lo(k) mod 2³²)·(hi(v)+hi(k) mod 2³²)。 -/
def nh32LaneK : Kernel where
  name := "nh32_lane"
  doc := "NH32 の 1 レーン: (lo(v)+lo(k) mod 2^32) * (hi(v)+hi(k) mod 2^32)。"
  params := [("v", .u64), ("k", .u64)]
  body := [
    ⟨.u64, "lo", (v64 "v" + v64 "k") &&& k64 0xffffffff⟩,
    ⟨.u64, "hi", ((v64 "v" >>> 32) + (v64 "k" >>> 32)) &&& k64 0xffffffff⟩]
  retTy := .u64
  ret := v64 "lo" * v64 "hi"

/-- NH64 の 1 組：((a+ka) mod 2⁶⁴)·((b+kb) mod 2⁶⁴)（128bit）。 -/
def nhPairK : Kernel where
  name := "nh_pair"
  doc := "NH64 の 1 組: ((a+ka) mod 2^64) * ((b+kb) mod 2^64)（128bit）。"
  params := [("a", .u64), ("b", .u64), ("ka", .u64), ("kb", .u64)]
  body := []
  retTy := .u128
  ret := ext (v64 "a" + v64 "ka") * ext (v64 "b" + v64 "kb")

/-- x mod p（x < 2⁶⁴ で (x mod 2⁶¹) + ⌊x/2⁶¹⌋ < 2p のとき。`mulmod` / `horner` の中ではつねに成り立つ）。 -/
def reduceK : Kernel where
  name := "reduce"
  doc := "x mod p（p = 2^61-1。(x mod 2^61) + (x >> 61) < 2p のとき）。"
  params := [("x", .u64)]
  body := reduceStmts "r" (v64 "x")
  retTy := .u64
  ret := v64 "r"

/-- a·b mod p（a, b < p）。 -/
def mulmodK : Kernel where
  name := "mulmod"
  doc := "a*b mod p（a, b < p）。"
  params := [("a", .u64), ("b", .u64)]
  body := mulmodStmts "m" (v64 "a") (v64 "b")
  retTy := .u64
  ret := v64 "m"

/-- Horner の 1 ステップ h·r + c mod p（h, r < p、c < 2⁶⁰）。 -/
def hornerK : Kernel where
  name := "horner"
  doc := "Horner の 1 ステップ h*r + c mod p（h, r < p、c < 2^63）。"
  params := [("h", .u64), ("r", .u64), ("c", .u64)]
  body := mulmodStmts "m" (v64 "h") (v64 "r") ++ reduceStmts "o" (v64 "m" + v64 "c")
  retTy := .u64
  ret := v64 "o"

/-- 128bit → 64bit の multiply-shift：⌊(m·x mod 2¹²⁸) / 2⁶⁴⌋。 -/
def msK : Kernel where
  name := "ms"
  doc := "128bit -> 64bit の multiply-shift: hi64(m*x mod 2^128)。"
  params := [("m", .u128), ("x", .u128)]
  body := []
  retTy := .u64
  ret := trunc ((v128 "m" * v128 "x") >>> 64)

/-- limb の 60bit マスク。 -/
def mask60 : Nat := 2 ^ 60 - 1

/-- v = x + 2⁶⁴·y の 60bit limb 0（v mod 2⁶⁰）。 -/
def limb0K : Kernel where
  name := "limb0"
  doc := "v = x + 2^64*y の limb 0: v mod 2^60。"
  params := [("x", .u64)]
  body := []
  retTy := .u64
  ret := v64 "x" &&& k64 mask60

/-- limb 1（⌊v/2⁶⁰⌋ mod 2⁶⁰）。 -/
def limb1K : Kernel where
  name := "limb1"
  doc := "v = x + 2^64*y の limb 1: floor(v/2^60) mod 2^60。"
  params := [("x", .u64), ("y", .u64)]
  body := []
  retTy := .u64
  ret := ((v64 "x" >>> 60) ||| (v64 "y" <<< 4)) &&& k64 mask60

/-- limb 2（⌊v/2¹²⁰⌋）。 -/
def limb2K : Kernel where
  name := "limb2"
  doc := "v = x + 2^64*y の limb 2: floor(v/2^120)。"
  params := [("y", .u64)]
  body := []
  retTy := .u64
  ret := v64 "y" >>> 56

/-- 仕上げ：fmix64(pre ^ fin)。fmix64 の本体を展開して持つ。 -/
def finishK : Kernel where
  name := "finish"
  doc := "仕上げ: fmix64(pre ^ fin)。"
  params := [("pre", .u64), ("fin", .u64)]
  body := ⟨.u64, "x", v64 "pre" ^^^ v64 "fin"⟩ :: fmix64K.body
  retTy := .u64
  ret := fmix64K.ret

/-- 出力する核の一覧（この順に出力する）。 -/
def kernels : List Kernel :=
  [fmix64K, finishK, nh32LaneK, nhPairK, reduceK, mulmodK, hornerK, msK, limb0K, limb1K, limb2K]

/-- どの核も整形（シフト量 < 幅、定数が幅に収まる、変数は定義済みで型が合う）。 -/
theorem kernels_wf : kernels.all Kernel.wf = true := by decide

end LeanHash.Impl
