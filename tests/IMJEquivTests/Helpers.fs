namespace IMJEquiv

open NUnit.Framework

[<AutoOpen>]
module Helpers =
  
  let ptm t = 
    try Parsing.term "" t with
    | Parser.ParseError (s,l,c) -> failwithf "Parse Error %d:%d: %s." l c s

  let pitbl t = 
    try Parsing.itbl "" t with
    | Parser.ParseError (s,l,c) -> failwithf "Parse Error %d:%d: %s." l c s

  let ptyenv t = 
    try Parsing.tyenv "" t with
    | Parser.ParseError (s,l,c) -> failwithf "Parse Error %d:%d: %s." l c s

  let ptytm t =
    try Parsing.tytm "" t with
    | Parser.ParseError (s,l,c) -> failwithf "Parse Error %d:%d: %s." l c s

  let AssertAlphaEqual (s: Term, t: Term) : Unit =
    if not (Term.alphaEq s t) then Assert.Fail ("Expected: {0}\n But was: {1}\n", s, t)
