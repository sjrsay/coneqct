#r @"..\..\packages\NUnit.2.6.3\lib\nunit.framework.dll"
#r @"..\..\bin\Utils.dll"
#r @"..\..\IMJEquiv\bin\Debug\IMJEquiv.exe"

open IMJEquiv
#load "Helpers.fs"
open IMJEquiv

let fn = System.IO.Path.Combine(__SOURCE_DIRECTORY__,"auto.dot")

let d = pitbl "I = { m:int -> int }, J = { n:int -> int }"
let g = ptyenv "cxt:J"
let t = ptm "new {z:I; m:\x.cxt.n(x)}"
let c = Canonical.canonise g t
let m = Move.ValM (Val.VReg 1)
let s = pstore "r1 : I = {}"
let a = Automata.fromCanon d g c [m] s
System.IO.File.WriteAllText(fn,Automata.toDot a)