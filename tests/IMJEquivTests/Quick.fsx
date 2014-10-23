#r @"..\..\packages\NUnit.2.6.3\lib\nunit.framework.dll"
#r @"..\..\bin\Utils.dll"
#r @"..\..\bin\IMJEquiv.exe"

open IMJEquiv
#load "Helpers.fs"
open IMJEquiv

let s = ptm "let x = 3 in x"
let t = ptm "let y = 3 in y"
Term.alphaEq s t

