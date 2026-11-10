/-
P3：HashIR の意味論。値は `BitVec`、演算は mod 2^w（Rust の `wrapping_*` と同じ）。

環境は型ごとに別の「名前 → 値」（`Env`）。文は順に環境を更新し、最後に戻り値の式を評価する。
-/
import LeanHash.IR.Syntax

namespace LeanHash.IR

/-- 環境（型ごとの名前空間）。 -/
structure Env where
  v64 : String → BitVec 64
  v128 : String → BitVec 128

namespace Env

def empty : Env := ⟨fun _ => 0, fun _ => 0⟩

def get : (t : Ty) → Env → String → t.denote
  | .u64, e, x => e.v64 x
  | .u128, e, x => e.v128 x

def set : (t : Ty) → Env → String → t.denote → Env
  | .u64, e, x, v => { e with v64 := fun y => if y = x then v else e.v64 y }
  | .u128, e, x, v => { e with v128 := fun y => if y = x then v else e.v128 y }

@[simp] theorem get_set_same (t : Ty) (e : Env) (x : String) (v : t.denote) :
    (e.set t x v).get t x = v := by
  cases t <;> simp [get, set]

@[simp] theorem get_set_ne (t : Ty) (e : Env) {x y : String} (h : y ≠ x) (v : t.denote) :
    (e.set t x v).get t y = e.get t y := by
  cases t <;> simp [get, set, h]

@[simp] theorem get_set_other : ∀ (t t' : Ty) (_ : t' ≠ t) (e : Env) (x y : String) (v : t.denote),
    (e.set t x v).get t' y = e.get t' y
  | .u64, .u64, h, _, _, _, _ => absurd rfl h
  | .u64, .u128, _, _, _, _, _ => rfl
  | .u128, .u64, _, _, _, _, _ => rfl
  | .u128, .u128, h, _, _, _, _ => absurd rfl h

end Env

/-- 二項演算の意味。 -/
def BinOp.eval {w : Nat} : BinOp → BitVec w → BitVec w → BitVec w
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .xor, a, b => a ^^^ b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b

/-- 型ごとの二項演算・シフト（`Ty.denote` を BitVec に開くため）。 -/
def Ty.bin : (t : Ty) → BinOp → t.denote → t.denote → t.denote
  | .u64, op, a, b => op.eval a b
  | .u128, op, a, b => op.eval a b

def Ty.shl : (t : Ty) → t.denote → Nat → t.denote
  | .u64, a, k => a <<< k
  | .u128, a, k => a <<< k

def Ty.shr : (t : Ty) → t.denote → Nat → t.denote
  | .u64, a, k => a >>> k
  | .u128, a, k => a >>> k

def Ty.lit : (t : Ty) → Nat → t.denote
  | .u64, n => BitVec.ofNat 64 n
  | .u128, n => BitVec.ofNat 128 n

/-- 式の値。 -/
def Expr.eval (e : Env) : {t : Ty} → Expr t → t.denote
  | t, .var x => e.get t x
  | t, .const n => t.lit n
  | t, .bin op a b => t.bin op (a.eval e) (b.eval e)
  | t, .shl a k => t.shl (a.eval e) k
  | t, .shr a k => t.shr (a.eval e) k
  | _, .ext a => (a.eval e).setWidth 128
  | _, .trunc a => (a.eval e).setWidth 64
  | _, .iteLt a b x y => if (a.eval e).toNat < (b.eval e).toNat then x.eval e else y.eval e

/-- 文を 1 つ実行する。 -/
def Stmt.exec (e : Env) (s : Stmt) : Env := e.set s.ty s.name (s.rhs.eval e)

/-- 核の値：引数を束縛した環境から文を順に実行し、戻り値を評価する。 -/
def Kernel.run (k : Kernel) (e : Env) : k.retTy.denote := k.ret.eval (k.body.foldl Stmt.exec e)

/-- 引数 1 つを u64 として束縛する。 -/
def Env.arg64 (e : Env) (x : String) (v : BitVec 64) : Env := e.set .u64 x v
def Env.arg128 (e : Env) (x : String) (v : BitVec 128) : Env := e.set .u128 x v

end LeanHash.IR
