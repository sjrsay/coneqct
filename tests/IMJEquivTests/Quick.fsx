#r @"..\..\packages\NUnit.2.6.3\lib\nunit.framework.dll"
#r @"..\..\bin\Utils.dll"
#r @"..\..\IMJEquiv\bin\Debug\IMJEquiv.exe"

open IMJEquiv
#load "Helpers.fs"
open IMJEquiv

let fn = System.IO.Path.Combine(__SOURCE_DIRECTORY__,"auto.dot")

let d = pitbl "Empty = { }, VarEmpty = { val: Empty }, Cell = { get:void -> Empty, set:Empty -> void }"
let g = ptyenv "v:VarEmpty, y:Empty"
let t = ptm "if y=null then skip else (v.val := y)"
let c = Canonical.canonise d g t
let m = [Move.ValM (Val.VReg 1); Move.ValM (Val.VReg 2)]
let s = pstore "r1 : VarEmpty = { val = null }, r2 : Empty = {}"
let a = Automata.fromCanon d g c m s
System.IO.File.WriteAllText(fn,Automata.toDot a)