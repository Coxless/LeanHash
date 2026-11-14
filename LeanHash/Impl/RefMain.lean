/-
`lake exe ref_vectors [出力先]`：参照実装 `hashCI`（`Outer.lean`。仕様との一致は `OuterEquiv.lean` の `hashCI_eq`）で
テストベクトルを出力する。Rust の `v2::hash_c` との差分テスト（`rust/leanhash/src/v2.rs` の `lean_ref`）に使う。

鍵は Rust の `v2::Keys::from_seed` と同じ手順（splitmix64）で作り、入力のバイト列も splitmix64 の下位 8bit で作る。
各行は `seed len hash`（16 進）。
-/
import LeanHash.Impl.Outer

open LeanHash.Impl

namespace LeanHash.Impl.Ref

/-- splitmix64（`rust/leanhash/src/lib.rs` の `splitmix64`）。新しい状態と出力。 -/
def splitmix64 (s : BitVec 64) : BitVec 64 × BitVec 64 :=
  let s := s + 0x9e3779b97f4a7c15#64
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9#64
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb#64
  (s, z ^^^ (z >>> 31))

/-- n 個の出力。 -/
def takeN (s : BitVec 64) : Nat → List (BitVec 64) × BitVec 64
  | 0 => ([], s)
  | n + 1 =>
    let (s, x) := splitmix64 s
    let (xs, s) := takeN s n
    (x :: xs, s)

/-- `r` の棄却サンプリング（61bit を取り、p 以上なら引き直す）。回数の上限つき。 -/
def drawR (s : BitVec 64) : Nat → BitVec 64 × BitVec 64
  | 0 => (0, s)
  | fuel + 1 =>
    let (s, x) := splitmix64 s
    let v := x >>> 3
    if v.toNat < pNat then (v, s) else drawR s fuel

/-- Rust の `v2::Keys::from_seed`。 -/
def keysFromSeed (seed : BitVec 64) : KeysI :=
  let (nh, s) := takeN seed 130
  let (s, hi) := splitmix64 s
  let (s, lo) := splitmix64 s
  let m := (hi.setWidth 128 <<< 64) ||| lo.setWidth 128 ||| 1#128
  let (r, s) := drawR s 1000
  let (s, fin) := splitmix64 s
  let (s, finMid) := splitmix64 s
  let (_, finLong) := splitmix64 s
  { nh := fun i => nh.getD i.val 0, m, r, fin, finMid, finLong }

/-- 入力のバイト列（splitmix64 の下位 8bit を n 個）。 -/
def bytesN (s : BitVec 64) : Nat → List (Fin 256) × BitVec 64
  | 0 => ([], s)
  | n + 1 =>
    let (s, x) := splitmix64 s
    let (bs, s) := bytesN s n
    (⟨x.toNat % 256, Nat.mod_lt _ (by decide)⟩ :: bs, s)

def hex64 (x : BitVec 64) : String :=
  let d := Nat.toDigits 16 x.toNat
  String.ofList (List.replicate (16 - d.length) '0' ++ d)

/-- 出力する長さ（経路の境界・端数の重ね読み・ブロック境界のまわり）。 -/
def lengths : List Nat :=
  List.range 41 ++ [63, 64, 65, 100, 127, 128, 129, 1000, 1016, 1017, 1023, 1024, 1025, 1026, 1031, 1032, 1033,
    1040, 2047, 2048, 2049, 2055, 2056, 2057, 3000, 3072, 3073, 4096, 5000]

def seeds : List (BitVec 64) := [1, 2, 3, 0xdeadbeef]

/-- 全ベクトル。入力の乱数状態は 0x1234 から始めて、seed・長さの順に続けて使う。 -/
def vectors : List String := Id.run do
  let mut st : BitVec 64 := 0x1234
  let mut out : List String := []
  for seed in seeds do
    let K := keysFromSeed seed
    for len in lengths do
      let (b, st') := bytesN st len
      st := st'
      out := s!"{hex64 seed} {len} {hex64 (hashCI K b)}" :: out
  return out.reverse

end LeanHash.Impl.Ref

def main (args : List String) : IO UInt32 := do
  let src := String.intercalate "\n" LeanHash.Impl.Ref.vectors ++ "\n"
  match args with
  | [] => IO.print src
  | [path] => IO.FS.writeFile path src
  | _ =>
    IO.eprintln "usage: lake exe ref_vectors [output.txt]"
    return 2
  return 0
