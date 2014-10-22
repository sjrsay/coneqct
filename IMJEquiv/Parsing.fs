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
