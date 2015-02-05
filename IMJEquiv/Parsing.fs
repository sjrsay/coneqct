module IMJEquiv.Parsing
open IMJEquiv

open Microsoft.FSharp.Text.Lexing
open Microsoft.FSharp.Text.Parsing

let private parse (fn: String) (f: (LexBuffer<Char> -> Parser.token) -> LexBuffer<Char> -> 'a) (s: String) : 'a =
  let lexbuf = LexBuffer<Char>.FromString s
  do lexbuf.EndPos <- { pos_bol = 0; pos_fname=fn; pos_cnum=0; pos_lnum=1 }
  f Lexer.tokenizeMain lexbuf

/// Given a file name `fn` (for error reporting purposes only) 
/// and text to be parsed `s`, `term fn s` is the term resulting
/// from parsing `s` or an exception.
let term (fn: String) (s: String) : Term = parse fn Parser.Term s

/// Given a file name `fn` (for error reporting purposes only) 
/// and text to be parsed `s`, `itbl fn s` is the interface table 
/// resulting from parsing `s` or an exception.
let itbl (fn: String) (s: String) : ITbl = parse fn Parser.ITbl s

/// Given a file name `fn` (for error reporting purposes only) 
/// and text to be parsed `s`, `tyenv fn s` is the type environment 
/// resulting from parsing `s` or an exception.
let tyenv (fn: String) (s: String) : TyEnv = parse fn Parser.TyEnv s

/// Given a file name `fn` (for error reporting purposes only) 
/// and text to be parsed `s`, `tyenv fn s` is the type environment 
/// resulting from parsing `s` or an exception.
let tytm (fn: String) (s: String) : TyEnv * Term = parse fn Parser.TyTerm s

/// Given a file name `fn` (for error reporting purposes only) 
/// and text to be parsed `s`, `store fn s` is the store 
/// resulting from parsing `s` or an exception.
let store (fn: String) (s: String) : Store = parse fn Parser.Store s

/// Given a file name `fn` (for error reporting purposes only) 
/// and text to be parsed `s`, `move fn s` is the list of moves 
/// resulting from parsing `s` or an exception.
let move (fn: String) (s: String) : List<Move> = parse fn Parser.Move s

let input (fn: String) : ITbl * TyEnv * Term * Term = 
  let str = System.IO.File.ReadAllText fn
  let d, g, tm1, tm2 = parse fn Parser.Input str
  let g' = 
    match g with
    | []   -> [("__cxt", Void)]
    | _::_ -> g
  (d, g', tm1, tm2)