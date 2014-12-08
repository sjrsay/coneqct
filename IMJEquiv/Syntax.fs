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

type CxtItem = 
  | IFaceDef of IntId * ITblDfn
  | Typing of Ident * Ty

type Cxt = List<CxtItem>

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Term =

  /// Given terms `s` and `t` with `s` having all variable names distinct 
  /// and `t` having all variable names distinct, `alphaEq s t` is `true`
  /// just if `s` and `t` are equal up to renaming of bound variables and
  /// is `false` otherwise.
  let alphaEq (s: Term) (t: Term) : Bool =
    
    let idCount = ref 0
    let nextId () = 
      idCount := !idCount + 1
      !idCount

    //
    // Note: alpha implements alpha equivalence as embodied by the rule:
    //   \x.M = \y.N   iff   M[z/x] = N[z/y]
    // for some fresh z.  Here the substitutions are delayed so that
    // M[z/x] is represented by the pair (z/x, M) and, additionally, z is 
    // represented as an integer for efficiency.
    //
    let rec alpha (uenv: Map<Ident, Int>) (venv: Map<Ident, Int>) (u: Term) (v: Term) =

      let checkIdents (x: Ident) (y: Ident) : Bool =
          match Map.tryFind x uenv, Map.tryFind y venv with
          // x and y are bound in s and t respectively
          | Some i, Some j -> i = j
          // x an y are free in s and t respectively
          | None, None     -> x = y
          // otherwise one is bound and the other free
          | _, _           -> false

      match u, v with
        | BVar x, BVar y -> checkIdents x y
        | Num i, Num j -> i = j
        | Skip, Skip -> true
        | Plus (m,n), Plus(p,q) 
        | Eq (m,n), Eq (p,q) 
        | While (m,n), While (p,q) 
        | Seq (m,n), Seq (p,q) -> alpha uenv venv m p && alpha uenv venv n q
        | VEq (x,y), VEq (a,b) -> checkIdents x a && checkIdents y b
        | Cond (m,n,p), Cond (q,r,s) -> 
            alpha uenv venv m q 
              && alpha uenv venv n r 
              && alpha uenv venv p s
        | Assn (m,f,n), Assn (p,g,q) -> f = g && alpha uenv venv m p && alpha uenv venv n q
        | Fld (m,f), Fld (n,g) -> f = g && alpha uenv venv m n
        | VFld (x,f), VFld (y,g) -> f = g && checkIdents x y
        | Call (m,mth,ms), Call (n,nth,ns) -> mth = nth && List.forall2 (alpha uenv venv) (m::ms) (n::ns)
        | Cast (i,m), Cast (j,n) -> i = j && alpha uenv venv m n
        | Let (x,b,m), Let (y,c,n) -> 
            let i = nextId ()
            let uenv' = Map.add x i uenv
            let venv' = Map.add y i venv
            alpha uenv venv b c && alpha uenv' venv' m n
        | LetCast (x,ii,y,m), LetCast (a,jj,b,n) ->
            let i = nextId ()
            let uenv' = Map.add x i uenv
            let venv' = Map.add a i venv
            ii = jj && checkIdents y b  && alpha uenv' venv' m n
        | LetCl (x,y,mth,ms,m), LetCl (a,b,nth,ns,n) ->
            let i = nextId ()
            let uenv' = Map.add x i uenv
            let venv' = Map.add a i venv
            mth = nth && checkIdents y b && List.forall2 (alpha uenv' venv') (m::ms) (n::ns)
        | New (x,ii,mths), New (y,jj,nths) ->
            let i = nextId ()
            let uenv' = Map.add x i uenv
            let venv' = Map.add y i venv
            ii = jj  && List.forall2 (alphaMeths uenv' venv') mths nths
        | Null, Null -> true
        | _, _ -> false

    and alphaMeths (uenv: Map<Ident,Int>) (venv: Map<Ident,Int>) (mth: MethSpec) (nth: MethSpec) : Bool =
      if mth.Name = nth.Name then
        let uenv', venv' = 
          List.fold2 (fun (m,n) x y -> let i = nextId () in (Map.add x i m, Map.add y i n)) (uenv, venv) mth.Vars nth.Vars
        alpha uenv' venv' mth.Body nth.Body
      else
        false

    alpha Map.empty Map.empty s t

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Cxt = 

  let separate (c:Cxt) : ITbl * TyEnv =
    let distinguish (ci: CxtItem) (m: ITbl, e: TyEnv) =
      match ci with
      | IFaceDef (i, d) -> (Map.add i d m, e)
      | Typing (x, t) -> (m, (x,t)::e)
    List.foldBack distinguish c (Map.empty, [])
