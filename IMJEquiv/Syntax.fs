namespace IMJEquiv
open IMJEquiv

/// The type of terms, follows the grammar of the paper.
[<StructuredFormatDisplayAttribute("{Show}")>]
type Term = 
  | BVar of Ident
  | Num of Int32
  | Skip
  | Plus of Term * Term
  | Eq of Term * Term
  | VEq of Ident * Ident
  | Seq of Term * Term
  | Cond of Term * Term * Term
  | Assn of Term * FldId * Term
  | Fld of Term * FldId
  | VFld of Ident * FldId
  | Call of Term * MethId * List<Term>
  | Cast of IntId * Term
  | Let of Ident * Term * Term
  | LetCast of Ident * IntId * Ident * Term
  | LetCl of Ident * Ident * MethId * List<Term> * Term
  | While of Term * Term
  | New of Ident * IntId * List<MethSpec>
  | Null 

  member x.Show = x.ToString ()

  override x.ToString () : String =
    match x with
    | Null -> "null"
    | BVar s -> s
    | Num n  -> n.ToString ()
    | Skip   -> "skip"
    | Plus (x,y) -> sprintf "%O + %O" x y
    | Eq (x,y) -> sprintf "%O = %O" x y
    | VEq (x,y) -> sprintf "%O = %O" x y
    | Seq (x,y) -> sprintf "%O; %O" x y
    | Cond (x,y,z) -> sprintf "if %O then %O else %O" x y z
    | Assn (x,f,y) -> sprintf "%O.%O := %O" x f y
    | Fld (s,f)  -> sprintf "%O.%O" s f
    | VFld (s,f) -> sprintf "%O.%O" s f
    | Call (x,m,ms) -> sprintf "%O.%O(%s)" x m (List.toStringWithDelims "" ", " "" ms)
    | Cast (s,x) -> sprintf "(%O)%O" s x
    | Let (s,x,y) -> sprintf "let %O = %O in %O" s x y
    | LetCast (x, i, y, m) -> sprintf "let %O = (%O)%O in %O" x i y m
    | LetCl (s,x,m,ms,b) -> sprintf "let %O = %O.%O(%s) in %O" s x m (List.toStringWithDelims "" ", " "" ms) b
    | While (x,y) -> sprintf "while %O do %O" x y
    | New (x,i,ms) -> sprintf "new { %O: %O; %s }" x i (List.toStringWithDelims "" ", " "" ms)


and [<StructuredFormatDisplay("{Show}")>] MethSpec = 
  {
    Name: Ident
    Vars: List<Ident> 
    Body: Term
  }

  member x.Show = x.ToString ()

  override x.ToString () : String =
    sprintf "%s: \\%s.%O" x.Name (List.toStringWithDelims "" " " "" x.Vars) x.Body

