namespace IMJEquiv

/// Canonical forms are defined in the paper by two mutually recursive
/// grammars, here represented as Canon and CanLet.  Additionally, CanMeth
/// packages up method specifications.
[<StructuredFormatDisplay("{Display}")>]
type Canon =
  | NullR
  | Var of Ident
  | NewR of Option<IntId> * Ident * IntId * List<CanMeth>
  | Let of Ident * CanLet * Canon
  | If of Ident * Canon * Canon

  member c.Display = c.ToString ()

  override c.ToString () : String =
    (Canon.ToTerm c).ToString ()

  // View a canonical form as a term.  This has to be a static method
  // because it is referenced by the method ToString ().
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

and CanMeth =
  {
    Name: MethId
    Vars: List<Ident>
    Body: Canon
  }

  override cm.ToString () : String =
    (CanMeth.ToMethSpec cm).ToString ()

  // View a canonical form method as a term method.  
  // This has to be a static method
  // because it is referenced by the method ToString ().
  static member ToMethSpec (cm: CanMeth) : MethSpec =
    {
      Name = cm.Name
      Vars = cm.Vars
      Body = Canon.ToTerm cm.Body
    }

and CanLet =
  | NullL of Ty
  | Num of Int32
  | Skip
  | Plus of Ident * Ident
  | Eq of Ident * Ident
  | Gre of Ident * Ident
  | Assn of Ident * FldId * Ident
  | Cast of IntId * Ident
  | Call of Ident * MethId * List<Ident>
  | Fld of Ident * FldId
  | While of Ident * Canon
  | NewB of Ident * IntId * List<CanMeth>

  override cl.ToString () : String =
    (CanLet.ToTerm cl).ToString ()

  // View a canonical let form as a term.  This has to be a static method
  // because it is referenced by the method ToString ().
  static member ToTerm (cl: CanLet) : Term =
    match cl with
    | NullL _ -> Term.Null
    | Num n -> Term.Num n
    | Skip -> Term.Skip
    | Plus (x,y) -> Term.Plus (BVar x, BVar y)
    | Gre (x,y) -> Term.Gre (BVar x, BVar y)
    | Eq (x,y) -> Term.VEq (x, y)
    | Assn (x,f,y) -> Term.Assn (BVar x, f, BVar y)
    | Cast (i,x) -> Term.Cast (i, BVar x)
    | Call (x,m,vs) -> Term.Call (BVar x, m, List.map BVar vs)
    | Fld (x,f) -> Term.VFld (x,f)
    | While (x,b) -> Term.While (Term.Fld (BVar x,"val"), Canon.ToTerm b)
    | NewB (x,i,ms) -> Term.New (x, i, List.map CanMeth.ToMethSpec ms)


module Canonical =

  /// A source of fresh variables.
  let private idCnt : Ref<Int32> = ref 0
  
  /// Returns a fresh variable.
  let private newVar () : Ident = 
    idCnt := !idCnt + 1;
    "x" + (!idCnt).ToString ()

  /// Given pair of identifiers (x,y) and identifier z
  /// returns [x/y]z.
  let private subIdent (x: Ident, y: Ident) (z: Ident) : Ident =
    if y = z then x else z

  /// Given a single variable renaming (x,y) and a canonical 
  /// form c, returns c[x/y].
  let rec subst (sub: Ident * Ident) (c: Canon) : Canon =
    match c with
    | NullR -> c  
    | Var x -> Var (subIdent sub x)
    | NewR (oi, x, i, ms) -> NewR (oi, x, i, List.map (subMeth sub) ms)
    | Let (x, cl, c) -> Let (x, subCanLet sub cl, subst sub c)
    | If (x, c1, c2) -> If (subIdent sub x, subst sub c1, subst sub c2)
  
  and subCanLet (sub: Ident * Ident) (c: CanLet) : CanLet =
    match c with
    | NullL _
    | Num _ 
    | Skip  -> c
    | Gre (x, y) -> Gre (subIdent sub x, subIdent sub y)
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

  /// Given an identifier x and two canonical forms cm and cm',
  /// returns the canonical form of let x = cm in cm'.  This is
  /// exactly the effective content of Lemma 34 from the original 
  /// draft of the paper.
  let rec private lemma34 (x: Ident) (cm: Canon) (cm': Canon) : Canon =
    match cm with
    | NullR -> NullR
    | Var y -> subst (y, x) cm'
    | NewR (oi, t, b, ms) ->
        let cmAsCanLet = NewB (t, b, ms) 
        match oi with
        | None -> Let (x, cmAsCanLet, cm')
        | Some i ->
            let y = newVar ()
            let cast = Cast (i, y) 
            let bdy = Let (x, cast, cm')
            Let (y, cmAsCanLet, bdy)
     | Let (y, clet, c') ->
         Let (y, clet, lemma34 x c' cm')
     | If (y, c1, c2) ->
         If (y, lemma34 x c1 cm', lemma34 x c2 cm')

  /// Given a mapping mp of identifiers to lists of methods, and a canonical form cm',
  /// returns a pair (cm'', b) where cm'' is cm' but with each call x.m(vs) replaced by
  /// the corresponding method body whenever m is in mp.[x].
  let rec private inlineCalls (mp: Map<Ident,List<CanMeth>>) (cm': Canon) : Canon * Bool =
    match cm' with
    | NullR -> (cm',false)
    | Var x ->  (cm',false)
    | NewR (oi, x, i, ns) -> 
        let ns',b = List.fold (fun (ns',b) n -> let n',b' = inlineCallsInMeth mp n in (n'::ns', b||b')) ([],false) ns
        (NewR (oi, x, i, ns'),b)
    | Let (z, cl, c) -> 
        match cl with 
        | Call (w, m, zs) when Map.containsKey w mp ->
            // This ignores potential casting problems   
            match List.tryFind (fun (n:CanMeth) -> n.Name = m) mp.[w] with
            | None     -> failwithf "Expected to find method %O" m 
            | Some mth ->
                let newcl = List.fold2 (fun b x y -> subst (x, y) b) mth.Body zs mth.Vars     
                (lemma34 z newcl c, true)
        | CanLet.NewB (b,i,ns) ->
            let mp' = Map.add z ns mp
            let cl',b1 = inlineCallsInCanLet mp cl
            let c', b2 = inlineCalls mp' c
            (Let (z, cl', c'), b1||b2) 
        | _ ->
            let mp' = 
              match cl with
              | Cast (_, y) -> 
                  match Map.tryFind y mp with
                  | None -> mp
                  | Some xs -> Map.add z xs mp
              | _           -> mp
            let cl',b1 = inlineCallsInCanLet mp cl
            let c', b2 = inlineCalls mp' c
            (Let (z, cl', c'), b1||b2)
    | If (x, c1, c2) -> 
        let c1',b1 = inlineCalls mp c1
        let c2',b2 = inlineCalls mp c2
        (If (x, c1', c2'), b1||b2)

  and private inlineCallsInCanLet (mp: Map<Ident,List<CanMeth>>) (cm': CanLet) : CanLet * Bool =
    match cm' with
    | NullL _
    | Num _ 
    | Skip  
    | Plus _ 
    | Gre _
    | Eq _ 
    | Assn _ 
    | Cast _ -> (cm',false)
    | Call (w, m, zs) -> (cm',false)
    | Fld (x, f)   -> (cm',false)
    | While (x, m) -> 
        let c',b = inlineCalls mp m
        (While (x, c'), b)
    | NewB (x, i, ns) -> 
        let ns',b = List.fold (fun (ns',b) n -> let n',b' = inlineCallsInMeth mp n in (n'::ns', b||b')) ([],false) ns
        (NewB (x, i, ns'), b)

  and private inlineCallsInMeth (mp: Map<Ident,List<CanMeth>>) (cm': CanMeth) : CanMeth * Bool =
    // Remove shadowed variables
    let mp' = Map.filter (fun k _ -> not <| List.contains k cm'.Vars) mp
    let body,b = inlineCalls mp' cm'.Body
    ({ cm' with Body = body }, b)

  /// Given a canonical form cm, returns cm but with
  /// all calls inlined.
  let inlineAllCalls (cm: Canon) : Canon =
    
    let rec fix (c: Canon) : Canon =
      let c',b = inlineCalls Map.empty c
      if b then fix c' else c'

    fix cm

  /// Given a canonical form c, returns c viewed as a term.
  let toTerm (c: Canon) : Term = Canon.ToTerm c

  /// Given a method in canonical form, returns the method viewed as a term.
  let methToTerm (cm: CanMeth) : MethSpec = CanMeth.ToMethSpec cm

  /// Given a canonical let form, returns the same viewed as a term.
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
    let assnLet  = Let (newVar (), Assn (y, "_val", z), whileLet)
    let constLet = Let (z, Num 1, assnLet)
    let newLet   = Let (y, NewB (newVar (), "_VarInt", []), constLet)
    newLet


  /// Given a canonical let form c, returns it lifted to
  /// a (normal) canonical form: let x = c in x.
  let private letout (c: CanLet) : Canon =
    let x = newVar () in Canon.Let (x,c,Var x)

  /// Given an interface table d, a type environment e and a term t,
  /// such that d,e |- t is in the fragment, returns the canonical form of t.
  /// Implementation follows the effective content of the proof from the paper.
  let rec canonise (d: ITbl) (e: TyEnv) (t: Term) : Canon =
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
        let let2 = lemma34 x' (canonise d e m') let1
        lemma34 x (canonise d e m) let2
    | Term.Gre (m, m') ->
        let x = newVar ()
        let x' = newVar ()
        let let1 = letout (Gre (x,x'))
        let let2 = lemma34 x' (canonise d e m') let1
        lemma34 x (canonise d e m) let2
    | Term.VEq (x, y) -> canonise d e (Term.Eq (BVar x,BVar y))
    | Term.Eq (m, m') ->
        let canm  = canonise d e m
        let canm' = canonise d e m'
        match (canm, canm') with
        | NewR _, _    -> canonise d e (Term.Num 0)
        | _, NewR _    -> canonise d e (Term.Num 0)
        | NullR, NullR -> canonise d e (Term.Num 0)
        | NullR, Var x
        | Var x, NullR ->
            let y = newVar ()
            let z = newVar ()
            let xTy =
              match TyEnv.tryLookup x e with
              | None    -> failwithf "Free variable %A in %A not given a type" x t
              | Some ty -> ty
            Let (y, NullL xTy, Let (z, Eq (x, y), Var z))
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
        lemma34 x (canonise d e m) (canonise d e m')
    | Term.Cond (m, m', m'') ->
        let x  = newVar ()    
        lemma34 x (canonise d e m) (If (x, canonise d e m', canonise d e m''))
    | Term.Assn (m, f, m') ->
        let x   = newVar ()
        let x'  = newVar ()
        let x'' = newVar ()
        let let2 = Let (x'', Assn (x,f,x'), Var x'')
        let let1 = lemma34 x' (canonise d e m') let2
        lemma34 x (canonise d e m) let1
    | Term.VFld (x,f) -> canonise d e (Term.Fld (BVar x, f))
    | Term.Fld (m, f) ->
        let cm = canonise d e m
        match cm with
        | NullR _ -> div
        | NewR (oi, t, r, ms) ->
            let fty = Type.ofFld d r f
            let dval = Val.defaultOfTy fty
            match dval with
            | VNul   -> Canon.NullR
            | VNum n -> letout (CanLet.Num n)
            | VStar  -> letout (CanLet.Skip)
            | VReg _ -> failwith "Not a possible default value"
        | Var x -> 
            letout (Fld (x, f))
        | Let (x, clet, c) ->
            let x' = newVar ()
            let v  = newVar ()
            let let1 = lemma34 x' c (Let (v, Fld(x',f), Var v))
            Let (x, clet, let1)
        | If (x, c1, c2) ->
            canonise d e (Term.Cond (BVar x, Term.Fld(toTerm c1, f), Term.Fld (toTerm c2, f)))
    | Term.Call (m, mth, ns) ->
        let cm = canonise d e m
        let cns = List.map (canonise d e) ns
        match cm with
        | NullR -> div
        | Var x -> 
            let zs = List.map (fun _ -> newVar ()) cns
            let v  = newVar ()
            let let1 = Let (v, Call (x, mth, zs), Var v)
            let lets = List.fold2 (fun l z n -> lemma34 z n l) let1 zs cns
            lets
        | NewR (oi, t, r, ms) ->
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
            canonise d e (Term.Cond (BVar x, Term.Call (toTerm c1, mth, tcns), Term.Call (toTerm c2, mth, tcns)))
        | Let (x, clet, c) ->
            Let (x, clet, canonise d e (Term.Call (toTerm c, mth, List.map toTerm cns)))
    | Term.Cast (i, m) ->
        let cm = canonise d e m
        match cm with
        | If (x, c1, c2) ->
            If (x, canonise d e (Term.Cast (i, toTerm c1)), canonise d e (Term.Cast (i, toTerm c2))) 
        | Let (x, clet, c) ->
            Let (x, clet, canonise d e (Term.Cast (i, toTerm c)))
        | NullR -> NullR
        | Var x -> 
            let y = newVar ()
            Let (y, Cast(i,x), Var y)
        | NewR (oi, t, r, ms) ->
            match oi with
            | None -> NewR (Some i, t, r, ms)
            | Some i' when Type.subtype d i' i -> 
                NewR (Some i, t, r, ms)
            | _ -> div
    | Term.LetCast (x, i, y, m) ->
        Let (x, Cast(i, y), canonise d e m)
    | Term.LetCl (x, y, mth, ns, m) ->
        let zs = List.map (fun _ -> newVar()) ns
        let cns = List.map (canonise d e) ns
        let bse = Let (x, Call(y, mth, zs), canonise d e m)
        let lets = List.fold2 (fun b z n -> lemma34 z n b) bse zs cns
        lets
    | Term.Let (x, m, m') ->
        lemma34 x (canonise d e m) (canonise d e m')
    | Term.While (m, m') ->
        let r = newVar ()
        let newVarInt = CanLet.NewB (newVar (),"_VarInt",[])
        let cm = canonise d e m
        let cm' = canonise d e m'
        let cmVar = newVar ()
        let rAssn = CanLet.Assn (r,"_val",cmVar)
        let rAssnLet = let x = newVar () in Canon.Let (x, rAssn, Var x)
        let bodyLet = lemma34 (newVar ()) cm' rAssnLet
        let whilec =  CanLet.While (r, bodyLet)
        let whilelet = let x = newVar () in Canon.Let (x, whilec, Var x)
        let inlet = Canon.Let (newVar (), rAssn, whilelet)
        let cmlet = lemma34 cmVar cm inlet
        let total = Canon.Let (r, newVarInt, cmlet)
        total
    | Term.New (t, r, ms) ->
        let canMeth (m: MethSpec) : CanMeth =
          let argTys, _ = Type.ofMeth d r m.Name
          let argTypings = List.zip m.Vars argTys
          let e' = e @ argTypings
          { Name = m.Name; Vars = m.Vars; Body = canonise d e' m.Body } 
        let cms = List.map canMeth ms
        NewR (None, t, r, cms)
