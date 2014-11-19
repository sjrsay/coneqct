module IMJEquiv.AutomatonTests

open NUnit.Framework

let fn = System.IO.Path.Combine(__SOURCE_DIRECTORY__,"auto.dot")

[<Test>]
let ``auto1`` () =
  let d = pitbl "I = { f: int, m:int -> int }"
  let g = ptyenv "cxt:void"
  let t = ptm "new {z:I; m:\x.x}"
  let c = Canonical.canonise g t
  let m = Move.ValM Val.VStar
  let s = pstore ""
  let a = Automata.fromCanon d g c [m] s
  System.IO.File.WriteAllText(fn,Automata.toDot a)