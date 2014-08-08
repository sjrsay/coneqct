/// This script is for very quickly testing things
/// it requires the solution to have been built before
/// in order for the referenced DLLs to be in place.

#r @"..\packages\FsLexYacc.Runtime.6.0.2\lib\net40\FsLexYacc.Runtime.dll"
#r @"..\..\Utils\bin\Debug\Utils.dll"

#load "Syntax.fs"
#load "Parser.fs"
#load "Lexer.fs"
#load "Parsing.fs"

open IMJEquiv

let pterm t = 
  try Parsing.term "" t with
  | Parser.ParseError (s,l,c) -> failwithf "Parse Error %d:%d: %s." l c s

pterm "3 + 4"
pterm "x := 3 + 4"
pterm "let x = 2 + 4 in x"
pterm "if (let x = 2 + 4 in x) then 3 else 6"
pterm "new { x : I; }"
pterm "new { x : I; m : \\x y.x }"
pterm "new { x : I; m1: \\x.x, m2: \\y.y  }"
pterm "new { x : I; m: \\x.let z = if b then 3 else 4 in z + 4 }"
pterm "y.assert(x.val = 2)"
pterm """
  let x = new { x : Varint; } in 
  new { z: I1;
    run: \u. if x.val = 0 then (x.val := 1; f.run(); x.assert(x.val=2)) else (if x.val=1 then x.val:=2 else div)
  }
"""
pterm "while (if b then 2 else 0) do skip"

