/-
P3：HashIR。計算の核（NH のレーン、多項式段の 1 ステップ、multiply-shift、fmix64）を書く小さな直線型 DSL。

- 型は u64 と u128 だけ（`Ty`）。値は `BitVec 64` / `BitVec 128`（`Ty.denote`）
- 演算はどれも Rust の `wrapping_*` / `as` / シフト / 比較と 1 対 1 に対応する（`EmitRust`）
- 核は「引数 → `let` の並び → 戻り値」の直線型プログラム（`Kernel`）。ループや分岐の文はまだない。
  条件分岐は式の `ite_lt`（`if a < b { x } else { y }`）だけ

Mathlib に依存しない（コード出力の実行ファイルを軽く保つため）。
-/

namespace LeanHash.IR

/-- 語の型。 -/
inductive Ty where
  | u64
  | u128
  deriving DecidableEq, Repr

/-- ビット幅。 -/
def Ty.width : Ty → Nat
  | .u64 => 64
  | .u128 => 128

/-- 値の型。 -/
abbrev Ty.denote : Ty → Type
  | .u64 => BitVec 64
  | .u128 => BitVec 128

/-- 二項演算（同じ型の 2 引数、mod 2^w の意味論）。 -/
inductive BinOp where
  | add | sub | mul | xor | and | or
  deriving DecidableEq, Repr

/-- 式。変数は名前で参照する（型ごとに別の名前空間）。 -/
inductive Expr : Ty → Type where
  | var {t : Ty} (x : String) : Expr t
  | const {t : Ty} (n : Nat) : Expr t
  | bin {t : Ty} (op : BinOp) (a b : Expr t) : Expr t
  /-- 定数ぶんの左シフト（k < 幅 であること。`Kernel.wf` で確かめる）。 -/
  | shl {t : Ty} (a : Expr t) (k : Nat) : Expr t
  /-- 定数ぶんの右シフト（論理シフト）。 -/
  | shr {t : Ty} (a : Expr t) (k : Nat) : Expr t
  /-- ゼロ拡張（Rust の `a as u128`）。 -/
  | ext (a : Expr .u64) : Expr .u128
  /-- 下位 64bit（Rust の `a as u64`）。 -/
  | trunc (a : Expr .u128) : Expr .u64
  /-- `if a < b { x } else { y }`（符号なし比較）。 -/
  | iteLt {t : Ty} (a b : Expr .u64) (x y : Expr t) : Expr t

/-- 文（`let x: t = e;`）。 -/
structure Stmt where
  ty : Ty
  name : String
  rhs : Expr ty

/-- 核：引数（すべて同じ名前空間）、文の並び、戻り値。 -/
structure Kernel where
  name : String
  doc : String
  params : List (String × Ty)
  body : List Stmt
  retTy : Ty
  ret : Expr retTy

/-! ### 構文の便利記法 -/

namespace Expr

def v64 (x : String) : Expr .u64 := .var x
def v128 (x : String) : Expr .u128 := .var x
def k64 (n : Nat) : Expr .u64 := .const n
def k128 (n : Nat) : Expr .u128 := .const n

instance {t : Ty} : Add (Expr t) := ⟨.bin .add⟩
instance {t : Ty} : Sub (Expr t) := ⟨.bin .sub⟩
instance {t : Ty} : Mul (Expr t) := ⟨.bin .mul⟩
instance {t : Ty} : XorOp (Expr t) := ⟨.bin .xor⟩
instance {t : Ty} : AndOp (Expr t) := ⟨.bin .and⟩
instance {t : Ty} : OrOp (Expr t) := ⟨.bin .or⟩
instance {t : Ty} : HShiftLeft (Expr t) Nat (Expr t) := ⟨.shl⟩
instance {t : Ty} : HShiftRight (Expr t) Nat (Expr t) := ⟨.shr⟩

/-! 記法を構成子に戻す（意味論の `simp` 用）。 -/
section
variable {t : Ty} (a b : Expr t) (k : Nat)
@[simp] theorem add_def : a + b = .bin .add a b := rfl
@[simp] theorem sub_def : a - b = .bin .sub a b := rfl
@[simp] theorem mul_def : a * b = .bin .mul a b := rfl
@[simp] theorem xor_def : a ^^^ b = .bin .xor a b := rfl
@[simp] theorem and_def : a &&& b = .bin .and a b := rfl
@[simp] theorem or_def : a ||| b = .bin .or a b := rfl
@[simp] theorem shl_def : a <<< k = .shl a k := rfl
@[simp] theorem shr_def : a >>> k = .shr a k := rfl
@[simp] theorem v64_def (x : String) : v64 x = .var x := rfl
@[simp] theorem v128_def (x : String) : v128 x = .var x := rfl
@[simp] theorem k64_def (n : Nat) : k64 n = .const n := rfl
@[simp] theorem k128_def (n : Nat) : k128 n = .const n := rfl
end

end Expr

/-! ### 整形性：シフト量が幅未満、定数が幅に収まる -/

def Expr.wf : {t : Ty} → Expr t → Bool
  | _, .var _ => true
  | t, .const n => n < 2 ^ t.width
  | _, .bin _ a b => a.wf && b.wf
  | t, .shl a k => a.wf && k < t.width
  | t, .shr a k => a.wf && k < t.width
  | _, .ext a => a.wf
  | _, .trunc a => a.wf
  | _, .iteLt a b x y => a.wf && b.wf && x.wf && y.wf

/-- 式が読む変数（名前と型）。 -/
def Expr.vars : {t : Ty} → Expr t → List (String × Ty)
  | t, .var x => [(x, t)]
  | _, .const _ => []
  | _, .bin _ a b => a.vars ++ b.vars
  | _, .shl a _ => a.vars
  | _, .shr a _ => a.vars
  | _, .ext a => a.vars
  | _, .trunc a => a.vars
  | _, .iteLt a b x y => a.vars ++ b.vars ++ x.vars ++ y.vars

/-- 読む変数がどれも、その時点で最後に束縛された同じ名前の変数と同じ型であること。
（Rust の `let` は名前を覆い隠すので、同じ名前を別の型で束縛し直すと意味論の「型ごとの名前空間」とずれる。それを禁じる） -/
def scopeOk (scope : List (String × Ty)) (vs : List (String × Ty)) : Bool :=
  vs.all fun (x, t) => scope.lookup x == some t

/-- 核の整形性：式がどれも整形で、変数は定義済みのものだけを正しい型で読む。 -/
def Kernel.wf (k : Kernel) : Bool :=
  let step := fun (acc : Bool × List (String × Ty)) (s : Stmt) =>
    (acc.1 && s.rhs.wf && scopeOk acc.2 s.rhs.vars, (s.name, s.ty) :: acc.2)
  let (ok, scope) := k.body.foldl step (true, k.params.reverse)
  ok && k.ret.wf && scopeOk scope k.ret.vars

end LeanHash.IR
