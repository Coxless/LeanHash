/-
`lake exe emit_rust [出力先]`：`Kernels.lean` の核を Rust に出力する（出力先を省略すると標準出力）。
-/
import LeanHash.IR.EmitRust
import LeanHash.Impl.Kernels

open LeanHash.IR LeanHash.Impl

def main (args : List String) : IO UInt32 := do
  unless kernels.all Kernel.wf do
    IO.eprintln "error: 整形でない核がある（Kernel.wf）"
    return 1
  let src := emitRust kernels
  match args with
  | [] => IO.print src
  | [path] => IO.FS.writeFile path src
  | _ =>
    IO.eprintln "usage: lake exe emit_rust [output.rs]"
    return 2
  return 0
