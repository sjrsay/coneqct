module IMJEquiv.AutomatonTests

open NUnit.Framework

let fn = System.IO.Path.Combine(__SOURCE_DIRECTORY__,"auto.dot")

//[<Test>]
let ``auto1`` () =
  let d = pitbl "I = { f: int, m:int -> int }"
  let g = ptyenv "cxt:void"
  let t = ptm "new {z:I; m:\x.x}"
  let c = Canonical.canonise d g t
  let m = Move.ValM Val.VStar
  let s = pstore ""
  let a = Automata.fromCanon d g c [m] s
  System.IO.File.WriteAllText(fn,Automata.toDot a)

//[<Test>]
let ``auto2`` () =
  let d = pitbl "I = { f: int, m:int -> int }"
  let g = ptyenv "cxt:I"
  let t = ptm "cxt.m(1)"
  let c = Canonical.canonise d g t
  let m = Move.ValM (Val.VReg 1)
  let s = pstore "r1 : I = {}"
  let a = Automata.fromCanon d g c [m] s
  System.IO.File.WriteAllText(fn,Automata.toDot a)

//[<Test>]
let ``auto3`` () =
  let d = pitbl "I = { m:int -> int }, J = { n:int -> int }"
  let g = ptyenv "cxt:J"
  let t = ptm "new {z:I; m:\x.cxt.n(x)}"
  let c = Canonical.canonise d g t
  let m = Move.ValM (Val.VReg 1)
  let s = pstore "r1 : I = {}"
  let a = Automata.fromCanon d g c [m] s
  System.IO.File.WriteAllText(fn,Automata.toDot a)

[<Test>]
let ``auto4`` () =
  let d = pitbl "Empty = { }, VarEmpty = { val: Empty }, Cell = { get:void -> Empty, set:Empty -> void }"
  let g = ptyenv "v:VarEmpty"
  let t = ptm "new {z:Cell; get:\x.v.val, set:\y.if y=null then skip else (v.val := y)}"
  let c = Canonical.canonise d g t
  let m = Move.ValM (Val.VReg 1)
  let s = pstore "r1 : VarEmpty = { val = null }"
  let a = Automata.fromCanon d g c [m] s
  System.IO.File.WriteAllText(fn,Automata.toDot a)

[<Test>]
let ``auto5`` () =
  let d = pitbl "Empty = { }, VarEmpty = { val: Empty }, Cell = { get:void -> Empty, set:Empty -> void }"
  let g = ptyenv "cxt:void"
  let t = ptm "let v = new {a:VarEmpty;} in new {z:Cell; get:\x.v.val, set:\y.if y=null then skip else (v.val := y)}"
  let c = Canonical.canonise d g t
  let m = Move.ValM (Val.VStar)
  let s = pstore ""
  let a = Automata.fromCanon d g c [m] s
  System.IO.File.WriteAllText(fn,Automata.toDot a)

