#r @"..\..\packages\NUnit.2.6.3\lib\nunit.framework.dll"
#r @"..\..\bin\Utils.dll"
#r @"..\..\bin\IMJEquiv.exe"

open IMJEquiv
#load "Helpers.fs"
open IMJEquiv

let fn = System.IO.Path.Combine(__SOURCE_DIRECTORY__,"auto.dot")

let d = pitbl "I = { f: int, m:int -> int }"
let g = ptyenv ""
let t = ptm "new {z:I; m:\x.x}"
let c = Canonical.canonise g t
let m = Move.ValM Val.VStar
let s = pstore ""
let a = Automata.fromCanon d g c [m] s
System.IO.File.WriteAllText(fn,Automata.toDot a)

ITbl.methods d "I"