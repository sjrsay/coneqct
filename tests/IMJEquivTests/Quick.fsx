#r @"..\..\packages\NUnit.2.6.3\lib\nunit.framework.dll"
#r @"..\..\bin\Utils.dll"
#r @"..\..\IMJEquiv\bin\Debug\IMJEquiv.exe"

open IMJEquiv
#load "Helpers.fs"
open IMJEquiv

let fn = System.IO.Path.Combine(__SOURCE_DIRECTORY__,"auto.dot")

let d = pitbl "VarInt = {val:int}"
let g = ptyenv "cxt:void"
let t = ptm "while 1 do skip"
let c = Canonical.canonise d g t
let m = Move.ValM Val.VStar
let s = pstore ""
let a = Automata.fromCanon d g c [m] s
System.IO.File.WriteAllText(fn,Automata.toDot a)