/-
P0 の最初の定理：xorshift（32bit 右シフトとの XOR）は 64bit で自己逆。
環境が正しく用意できたかの確認用（`lake build` が通れば Lean + bv_decide が動いている）。
-/
import Std.Tactic.BVDecide

namespace LeanHash.Spec

def xs (x : BitVec 64) : BitVec 64 := x ^^^ (x >>> 32)

theorem xs_involutive (x : BitVec 64) : xs (xs x) = x := by
  unfold xs; bv_decide

end LeanHash.Spec
