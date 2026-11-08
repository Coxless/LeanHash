/-
P1 仕上げ段：MurmurHash3 の fmix64 の仕様・逆関数・全単射。

Rust 側の試作（`rust/leanhash/src/lib.rs` の `fmix64`）と同じ定義。
証明の方針（CLAUDE.md）:
- 64bit 乗算は `bv_decide` に投げない。奇数定数 c とその逆元 c⁻¹（c * c⁻¹ = 1 mod 2⁶⁴）を
  具体値の計算で確かめ、結合則で打ち消す
- `bv_decide` は xorshift（シフトと XOR）だけに使う
-/
import Std.Tactic.BVDecide

namespace LeanHash.Spec

/-- 右シフト s との XOR（xorshift）。 -/
def xsr (s : Nat) (x : BitVec 64) : BitVec 64 := x ^^^ (x >>> s)

/-- シフト量が 32 以上なら xorshift は自己逆（上位の s ビットは 1 回目で変わらないため）。 -/
theorem xsr33_involutive (x : BitVec 64) : xsr 33 (xsr 33 x) = x := by
  unfold xsr; bv_decide

/-- fmix64 の乗算定数。 -/
def c1 : BitVec 64 := 0xff51afd7ed558ccd#64
def c2 : BitVec 64 := 0xc4ceb9fe1a85ec53#64

/-- それぞれの mod 2⁶⁴ での逆元（定数は奇数なので存在する）。 -/
def c1Inv : BitVec 64 := 0x4f74430c22a54005#64
def c2Inv : BitVec 64 := 0x9cb4b2f8129337db#64

theorem c1_mul_c1Inv : c1 * c1Inv = 1#64 := by decide
theorem c2_mul_c2Inv : c2 * c2Inv = 1#64 := by decide

/-- a * b = 1 なら、b を掛けると a を掛けたのが打ち消される（結合則だけで示す）。 -/
theorem mul_mul_cancel {a b : BitVec 64} (h : a * b = 1#64) (x : BitVec 64) :
    x * a * b = x := by
  rw [BitVec.mul_assoc, h, BitVec.mul_one]

/-- MurmurHash3 の fmix64。 -/
def fmix64 (x : BitVec 64) : BitVec 64 :=
  xsr 33 (xsr 33 (xsr 33 x * c1) * c2)

/-- fmix64 の逆関数。各段を逆順に戻す。 -/
def fmix64Inv (x : BitVec 64) : BitVec 64 :=
  xsr 33 (xsr 33 (xsr 33 x * c2Inv) * c1Inv)

theorem fmix64Inv_fmix64 (x : BitVec 64) : fmix64Inv (fmix64 x) = x := by
  simp only [fmix64, fmix64Inv, xsr33_involutive,
    mul_mul_cancel c2_mul_c2Inv, mul_mul_cancel c1_mul_c1Inv]

theorem fmix64_fmix64Inv (x : BitVec 64) : fmix64 (fmix64Inv x) = x := by
  have h1 : c1Inv * c1 = 1#64 := by rw [BitVec.mul_comm]; exact c1_mul_c1Inv
  have h2 : c2Inv * c2 = 1#64 := by rw [BitVec.mul_comm]; exact c2_mul_c2Inv
  simp only [fmix64, fmix64Inv, xsr33_involutive, mul_mul_cancel h1, mul_mul_cancel h2]

theorem fmix64_injective : Function.Injective fmix64 := fun x y h => by
  rw [← fmix64Inv_fmix64 x, ← fmix64Inv_fmix64 y, h]

theorem fmix64_surjective : Function.Surjective fmix64 := fun y =>
  ⟨fmix64Inv y, fmix64_fmix64Inv y⟩

/-- P1 のゲート：fmix64 は全単射（Mathlib の `Function.Bijective` の定義そのもの。
仕様層を Mathlib に依存させないため、単射 ∧ 全射 の形で書く）。 -/
theorem fmix64_bijective : Function.Injective fmix64 ∧ Function.Surjective fmix64 :=
  ⟨fmix64_injective, fmix64_surjective⟩

/-! Rust の試作との照合（値は `rust/leanhash` の `fmix64_matches_lean_vectors` と同じ）。 -/

example : fmix64 0x0000000000000000#64 = 0x0000000000000000#64 := by decide
example : fmix64 0x0000000000000001#64 = 0xb456bcfc34c2cb2c#64 := by decide
example : fmix64 0x8000000000000000#64 = 0x8f780810af31a493#64 := by decide
example : fmix64 0x0123456789abcdef#64 = 0x87cbfbfe89022cea#64 := by decide
example : fmix64 0xffffffffffffffff#64 = 0x64b5720b4b825f21#64 := by decide
example : fmix64Inv 0xb456bcfc34c2cb2c#64 = 0x0000000000000001#64 := by decide
example : fmix64Inv 0x8f780810af31a493#64 = 0x8000000000000000#64 := by decide

end LeanHash.Spec
