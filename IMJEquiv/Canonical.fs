namespace IMJEquiv
open IMJEquiv

[<StructuredFormatDisplayAttribute("{Show}")>]
type Canon =
  | NullR
  | Var of Ident
  | NewR of Option<IntId> * Ident * IntId * List<CanMeth>
  | Let of Ident * CanLet * Canon
  | If of Ident * Canon * Canon

  member c.Show : String =
    c.ToString ()

  override c.ToString () : String =
    (Canon.ToTerm c).ToString ()

  static member ToTerm (c: Canon) : Term =
    match c with
    | NullR -> Term.Null
    | NewR (o,x,i,ms) -> 
        let newtm = Term.New (x,i, List.map CanMeth.ToMethSpec ms)
        match o with
        | None -> newtm
        | Some j -> Term.Cast (j, newtm)
    | Var x -> BVar x
    | Let (x,m,b) -> Term.Let (x, CanLet.ToTerm m, Canon.ToTerm b)
    | If (x,t,f) -> Cond (BVar x, Canon.ToTerm t, Canon.ToTerm f)

and [<StructuredFormatDisplayAttribute("{Show}")>] CanMeth =
  {
    Name: MethId
    Vars: List<Ident>
    Body: Canon
  }

  member cm.Show : String =
    cm.ToString ()

  override cm.ToString () : String =
    (CanMeth.ToMethSpec cm).ToString ()

  static member ToMethSpec (cm: CanMeth) : MethSpec =
    {
      Name = cm.Name
      Vars = cm.Vars
      Body = Canon.ToTerm cm.Body
    }

and [<StructuredFormatDisplayAttribute("{Show}")>] CanLet =
  | NullL
  | Num of Int32
  | Skip
  | Plus of Ident * Ident
  | Eq of Ident * Ident
  | Assn of Ident * FldId * Ident
  | Cast of IntId * Ident
  | Call of Ident * MethId * List<Ident>
  | Fld of Ident * FldId
  | While of Ident * Canon
  | NewB of Ident * IntId * List<CanMeth>

  member cl.Show : String =
    cl.ToString ()

  override cl.ToString () : String =
    (CanLet.ToTerm cl).ToString ()

  static member ToTerm (cl: CanLet) : Term =
    match cl with
    | NullL -> Term.Null
    | Num n -> Term.Num n
    | Skip -> Term.Skip
    | Plus (x,y) -> Term.Plus (BVar x, BVar y)
    | Eq (x,y) -> Term.VEq (x, y)
    | Assn (x,f,y) -> Term.Assn (BVar x, f, BVar y)
    | Cast (i,x) -> Term.Cast (i, BVar x)
    | Call (x,m,vs) -> Term.Call (BVar x, m, List.map BVar vs)
    | Fld (x,f) -> Term.VFld (x,f)
    | While (x,b) -> Term.While (BVar x, Canon.ToTerm b)
    | NewB (x,i,ms) -> Term.New (x, i, List.map CanMeth.ToMethSpec ms)


module Canonical =

  let private idCnt : Ref<Int32> = ref 0
  
  let newVar () : Ident = 
    idCnt := !idCnt + 1;
    "x" + (!idCnt).ToString ()

  let subIdent (x: Ident, y: Ident) (z: Ident) : Ident =
    if x = z then y else x

  let rec subst (sub: Ident * Ident) (c: Canon) : Canon =
    match c with
    | NullR -> c  
    | Var x -> Var (subIdent sub x)
    | NewR (oi, x, i, ms) -> NewR (oi, x, i, List.map (subMeth sub) ms)
    | Let (x, cl, c) -> Let (x, subCanLet sub cl, subst sub c)
    | If (x, c1, c2) -> If (subIdent sub x, subst sub c1, subst sub c2)
  
  and subCanLet (sub: Ident * Ident) (c: CanLet) : CanLet =
    match c with
    | NullL 
    | Num _ 
    | Skip  -> c
    | Plus (x, y) -> Plus (subIdent sub x, subIdent sub y)
    | Eq (x, y) -> Eq (subIdent sub x, subIdent sub y)
    | Assn (x, f, z) -> Assn (subIdent sub x, f, subIdent sub z)
    | Cast (i, x) -> Cast (i, subIdent sub x)
    | Call (x, m, zs) -> Call (subIdent sub x, m, List.map (subIdent sub) zs)
    | Fld (x, f) -> Fld (subIdent sub x, f)
    | While (x, m) -> While (subIdent sub x, subst sub m)
    | NewB (x, i, ms) -> NewB (subIdent sub x, i, List.map (subMeth sub) ms) 

  and subMeth (sub: Ident * Ident) (m: CanMeth) : CanMeth =
    {
      m with 
        Body = subst sub m.Body
    }

  let rec inlineCalls (ms: List<CanMeth>) (xs: List<Ident>) (cm': Canon) : Canon =
    match cm' with
    | NullR -> cm'  
    | Var x ->  cm'
    | NewR (oi, x, i, ns) -> NewR (oi, x, i, List.map (inlineCallsInMeth ms xs) ns)
    | Let (z, cl, c) -> 
        match cl with 
        | Call (w, m, zs) when List.contains w xs ->
            // This ignores potential casting problems   
            match List.tryFind (fun (n:CanMeth) -> n.Name = m) ms with
            | None     -> failwithf "Expected to find method %O" m 
            | Some mth ->
                let newcl = List.fold2 (fun b x y -> subst (x, y) b) mth.Body mth.Vars zs     
                lemma34 z newcl c
        | _ ->
            let xs' = 
              match cl with
              | Cast (_, y) -> if List.contains y xs then z::xs else xs 
              | _           -> xs
            Let (z, inlineCallsInCanLet ms xs cl, inlineCalls ms xs' c)
    | If (x, c1, c2) -> If (x, inlineCalls ms xs c1, inlineCalls ms xs c2)

  and inlineCallsInCanLet (ms: List<CanMeth>) (xs: List<Ident>) (cm': CanLet) : CanLet =
    match cm' with
    | NullL 
    | Num _ 
    | Skip  
    | Plus _ 
    | Eq _ 
    | Assn _ 
    | Cast _ -> cm'
    | Call (w, m, zs) -> cm'
    | Fld (x, f)   -> cm'
    | While (x, m) -> While (x, inlineCalls ms xs m)
    | NewB (x, i, ns) -> NewB (x, i, List.map (inlineCallsInMeth ms xs) ns) 

  and inlineCallsInMeth (ms: List<CanMeth>) (xs: List<Ident>) (cm': CanMeth) : CanMeth =
    {
      cm' with
        Body = inlineCalls ms xs cm'.Body
    }

  and lemma34 (x: Ident) (cm: Canon) (cm': Canon) : Canon =
    match cm with
    | NullR -> NullR
    | Var y -> subst (y, x) cm'
    | NewR (oi, t, b, ms) ->
        let cmAsCanLet = NewB (t, b, ms) 
        let newcm' =  inlineCalls ms [x] cm'
        match oi with
        | None -> Let (x, cmAsCanLet, newcm')
        | Some i ->
            let y = newVar ()
            let cast = Cast (i, y) 
            let bdy = Let (x, cast, newcm')
            Let (y, cmAsCanLet, bdy)
     | Let (y, clet, c') ->
         Let (y, clet, lemma34 x c' cm')
     | If (y, c1, c2) ->
         If (y, lemma34 x c1 cm', lemma34 x c2 cm')

  // The following three are defined as static members only so
  // that the ToString () and Show machinery can make use of them
  // for the purpose of displaying canonical forms during
  // interaction and debugging.
  let toTerm (c: Canon) : Term = Canon.ToTerm c
  let methToTerm (cm: CanMeth) : MethSpec = CanMeth.ToMethSpec cm
  let canLetToTerm (cl: CanLet) : Term = CanLet.ToTerm cl

  /// The canonical form for divergence `div` is exactly
  ///    `let y = new {_: VarInt} in 
  ///     let z = 1 in
  ///     let _ = y.val := z in
  ///     let x = while y.val do (let u = skip in u) in 
  ///     x`
  /// i.e. the canonical form of `while 1 do skip`.
  let div : Canon = 
    let y = newVar ()
    let x = newVar ()
    let z = newVar ()
    let u = newVar ()
    let skipLet  = Let (u, Skip, Var u)
    let whileLet = Let (x, While (y, skipLet), Var x)
    let assnLet  = Let (newVar (), Assn (y, "val", z), whileLet)
    let constLet = Let (z, Num 1, assnLet)
    let newLet   = Let (y, NewB (newVar (), "VarInt", []), constLet)
    newLet

  let rec canonise (t: Term) : Canon =
    match t with
    | BVar x -> Var x
    | Null -> NullR
    | Term.Num i ->  
        let x = newVar ()
        Let (x, Num i, Var x)
    | Term.Skip -> 
        let x = newVar ()
        Let (x, Skip, Var x)
    | Term.Plus (m, m') ->
        let x   = newVar ()
        let x'  = newVar ()
        let x'' = newVar ()
        let let1 = Let (x'', Plus (x, x'), Var x'')
        let let2 = lemma34 x' (canonise m') let1
        lemma34 x (canonise m) let2
    | Term.Eq (m, m') ->
        let canm  = canonise m
        let canm' = canonise m'
        match (canm, canm') with
        // This needs to check for casting errors
        | NewR _, _    -> canonise (Term.Num 0)
        | _, NewR _    -> canonise (Term.Num 0)
        | NullR, NullR -> canonise (Term.Num 0)
        | NullR, Var x
        | Var x, NullR ->
            let y = newVar ()
            let z = newVar ()
            Let (y, NullL, Let (z, Eq (x, y), Var z))
        | Var x1, Var x2 ->
            let z = newVar ()
            Let (z, Eq (x1, x2), Var z)
        | Let (x,c1,c2), m 
        | m, Let (x,c1,c2) ->
            let y = newVar ()
            let z = newVar ()
            let v = newVar ()
            let let2 = lemma34 y c2 (Let (v, Eq (y, z), Var v))
            let let1 = Let (x, c1, let2)
            lemma34 z m let1
        | If (x,c1,c2), m 
        | m, If (x,c1,c2) ->
            let y1 = newVar ()
            let y2 = newVar ()
            let z = newVar ()
            let v1 = newVar ()
            let v2 = newVar ()
            let let1 = lemma34 y1 c1 (Let (v1, Eq (y1, z), Var v1))
            let let2 = lemma34 y2 c2 (Let (v2, Eq (y2, z), Var v2))
            lemma34 z m (If (x, let1, let2))
    | Term.Seq (m, m') ->
        let x = newVar ()
        lemma34 x (canonise m) (canonise m')
    | Term.Cond (m, m', m'') ->
        let x  = newVar ()    
        lemma34 x (canonise m) (If (x, canonise m', canonise m''))
    | Term.Assn (m, f, m') ->
        let x   = newVar ()
        let x'  = newVar ()
        let x'' = newVar ()
        let let2 = Let (x'', Assn (x,f,x'), Var x'')
        let let1 = lemma34 x' (canonise m') let2
        lemma34 x (canonise m) let1
    | Term.Fld (m, f) ->
        let cm = canonise m
        match cm with
        | NullR -> div
        | NewR (oi, t, r, ms) ->
            // Need to know type of r.f in order to return default value
            // also possible divergence due to mis-casting
            div
        | Var x -> 
            let x' = newVar ()
            Let (x', Fld (x, f), Var x')
        | Let (x, clet, c) ->
            let x' = newVar ()
            let v  = newVar ()
            let let1 = lemma34 x' c (Let (v, Fld(x',f), Var v))
            Let (x, clet, let1)
        | If (x, c1, c2) ->
            canonise (Term.Cond (BVar x, Term.Fld(toTerm c1, f), Term.Fld (toTerm c2, f)))
    | Term.Call (m, mth, ns) ->
        let cm = canonise m
        let cns = List.map canonise ns
        match cm with
        | NullR -> div
        | Var x -> 
            let zs = List.map (fun _ -> newVar ()) cns
            let v  = newVar ()
            let let1 = Let (v, Call (x, mth, zs), Var v)
            let lets = List.fold2 (fun l z n -> lemma34 z n l) let1 zs cns
            lets
        | NewR (oi, t, r, ms) ->
            // Have to account for casting errors here
            match List.tryFind (fun (p: CanMeth) -> p.Name = mth) ms with
            | None -> div
            | Some p -> 
                let zs = List.map (fun _ -> newVar ()) cns
                let v  = newVar ()
                let newbdy = List.fold2 (fun b x y -> subst (x, y) b) p.Body p.Vars zs
                let lets = List.fold2 (fun l z n -> lemma34 z n l) newbdy zs cns
                lets
        | If (x, c1, c2) ->  
            let tcns = List.map toTerm cns
            canonise (Term.Cond (BVar x, Term.Call (toTerm c1, mth, tcns), Term.Call (toTerm c2, mth, tcns)))
        | Let (x, clet, c) ->
            Let (x, clet, canonise (Term.Call (toTerm c, mth, List.map toTerm cns)))
    | Term.Cast (i, m) ->
        let cm = canonise m
        match cm with
        | If (x, c1, c2) ->
            If (x, canonise (Term.Cast (i, toTerm c1)), canonise (Term.Cast (i, toTerm c2))) 
        | Let (x, clet, c) ->
            Let (x, clet, canonise (Term.Cast (i, toTerm c)))
        | NullR -> NullR
        | Var x -> 
            let y = newVar ()
            Let (y, Cast(i,x), Var y)
        | NewR (oi, t, r, ms) ->
            // Check relationship between oi and i
            NewR (Some i, t, r, ms)
    | Term.LetCast (x, i, y, m) ->
        Let (x, Cast(i, y), canonise m)
    | Term.LetCl (x, y, mth, ns, m) ->
        let zs = List.map (fun _ -> newVar()) ns
        let cns = List.map canonise ns
        let bse = Let (x, Call(y, mth, zs), canonise m)
        let lets = List.fold2 (fun b z n -> lemma34 z n b) bse zs cns
        lets
    | Term.Let (x, m, m') ->
        lemma34 x (canonise m) (canonise m')
    | Term.While (m, m') ->
        // We need the varint type here
        div
    | Term.New (t, r, ms) ->
        let canMeth (m: MethSpec) : CanMeth =
          { Name = m.Name; Vars = m.Vars; Body = canonise m.Body } 
        let cms = List.map canMeth ms
        NewR (None, t, r, cms)
