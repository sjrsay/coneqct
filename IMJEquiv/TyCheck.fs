module IMJEquiv.TyCheck

// The type checking module implements an efficient formulation of Hindley Milner
// as described in the paper "Practical Type Inference for Arbitrary Rank Types"
// by Peyton Jones, Vytiniotis, Weirich and Shields.  Note: the extension to
// arbitrary ranks is not implemented.
//
// For the purpose of typing objects, we extend the possible types with shape (NullTy x)
// in which x is a type variable, to represent the type of a naked occurrence of null.  
// This type acts in the same way as a usual type variable (Var x) except that we ensure 
// that it cannot be unified with int or void.
//

// Types extended by type variables
// for the purposes of unification.
type ETy =
  | Void
  | Int
  | Obj of IntId
  | Var of TyVar
  | NullTy of TyVar

  override x.ToString () =
    match x with
    | Void -> "void"
    | Int -> "int"
    | Obj ei -> ei.ToString ()
    | Var tv -> tv.ToString ()
    | NullTy tv -> tv.ToString ()

  member t.Zonk () =
    match t with 
    | Var x -> x.Zonk ()
    | _ -> t

/// Type variables for unification have 
/// a reference which is filled in upon
/// unification.
and TyVar =
  {
    Name : Int
    Inst : Ref<Option<ETy>>
  }

  /// Flatten chains of references built
  /// up during unification.
  member x.Zonk () =
    match !x.Inst with
    | None -> Var x
    | Some t' ->
        let t'' = t'.Zonk ()
        do x.Inst := Some t''
        t''

  override x.ToString () =
    let t = x.Zonk ()
    match t with
    | Var tv ->
        "a" + tv.Name.ToString ()
    | _ -> t.ToString ()


type ETyEnv = List<Ident * ETy>

exception UnifyError

/// A source for new type variables
let private tyVarNum = ref 0

/// newTyVar returns a fresh type variable
let private newTyVar () : TyVar =
  do incr tyVarNum
  { Inst = ref None; Name = !tyVarNum }

/// Given an identifier x and an extended type environment e,
/// returns Some t if t is the type of x in e and None if 
/// x not in domain of e.
let private lookup (x: Ident) (e: ETyEnv) : Option<ETy> =
  List.foldBack (fun (y,ty) opt -> match opt with Some _ -> opt | None -> if x = y then Some ty else None) e None

/// Lift a type to an extended type trivially.
let private fromTy (t: Ty) : ETy =
  match t with
  | Ty.Void    -> Void
  | Ty.Int     -> Int
  | Ty.Iface i -> Obj i

/// Flatten chains of references built up during unification.
let rec private zonk (t: ETy) : ETy =
  t.Zonk ()

/// Given extended types t1 and t2, destructively updates
/// t1 and t2 in order to unify them or, if they
/// are not unifiable raises a UnifyError
let rec unify (t1: ETy) (t2: ETy) : Unit =
  match t1, t2 with 
  | _, _ when t1 = t2 -> ()
  | Var x,    _        -> unifyVar x t2
  | _,        Var y    -> unifyVar y t1 
  | NullTy x, NullTy _ -> unifyVar x t2
  | NullTy x, Obj _    -> unifyVar x t2
  | NullTy _, NullTy y -> unifyVar y t1
  | Obj _,    NullTy y -> unifyVar y t1
  | _,        _        -> raise UnifyError

and private unifyVar (tv: TyVar) (t: ETy) : Unit =
  match !tv.Inst with
  | None -> unifyUnboundVar tv t
  | Some t' -> unify t' t

and private unifyUnboundVar (tv: TyVar) (t: ETy) : Unit =
  match t with
  | Var x -> 
      match !x.Inst with
      | None -> tv.Inst := Some t
      | Some t' -> unifyUnboundVar tv (zonk t')
  | _ ->
      tv.Inst := Some t

/// Given an interface table d, a type environment g, a term t and a type ty,
/// succeeds silently just if d,g |- t : ty and raises a TypeError otherwise.
let rec private check (d: ITbl) (g: ETyEnv) (t: Term) (ty: ETy) : Unit =

  let varLkup x =
    match lookup x g with
    | None -> raise (TypeError (sprintf "Variable %O not declared in the context." x))
    | Some ty -> ty

  // I'm not sure what is right way to do OO type inference,
  // but there must be a better way to do this...
  let getIface (t: ETy) : IntId =
    let t' = zonk t
    match t' with
    | Obj ifc -> ifc
    | _ -> raise (TypeError (sprintf "Expected interface for method resolution but found %O." t))

  let ety: ETy =
    match t with
    | BVar x -> varLkup x    
    | Num _  -> Int
    | MaxInt -> Int
    | Skip   -> Void
    | Minus (m,n)
    | Plus (m,n) ->
        do check d g m Int
        do check d g n Int
        Int
    | Gre (m,n) ->
        do check d g m Int
        do check d g n Int
        Int
    | Eq (m,n) ->
        let mTy = infer d g m
        do check d g n mTy
        Int
    | VEq (x,y) ->
        let xTy = varLkup x
        let yTy = varLkup y
        try unify xTy yTy with
        | UnifyError -> raise (TypeError (sprintf "Could not unify types %O and %O for term %O." xTy yTy t))
        Int
    | Seq (m,n) ->
        do check d g m Void
        infer d g n
    | Cond (m,n,p) ->
        do check d g m Int
        let nTy = infer d g n
        check d g p nTy
        nTy
    | Assn (m,f,n) -> 
        let mTy = infer d g m
        let mI  = getIface mTy
        let fTy = Type.ofFld d mI f
        check d g n (fromTy fTy)
        Void
    | Fld (m,f) ->
        let mTy = infer d g m
        let mI  = getIface mTy
        fromTy (Type.ofFld d mI f)
    | VFld (x,f) ->
        let xTy = varLkup x
        let xI  = getIface xTy
        let opt = Type.tryOfFld d xI f
        match opt with
        | Some ty -> fromTy ty
        | None -> raise (TypeError (sprintf "Field %s is not in the interface %O of object %O" f xI x))
    | Call (m,mth,ns) ->
        let mTy = infer d g m
        let mI  = getIface mTy
        let opt = Type.tryOfMeth d mI mth
        match opt with
        | Some (argTys,resTy) ->
            do List.iter2 (fun n a -> check d g n (fromTy a)) ns argTys
            fromTy resTy
        | None -> raise (TypeError (sprintf "Method %s is not in the interface %O of object %O" mth mI m))
    | Cast (j,m) ->
        let mTy = infer d g m
        let mI  = getIface mTy
        if Type.subtype d mI j || Type.subtype d j mI then
          Obj j
        else
          raise (TypeError (sprintf "Invalid cast %O" t))
    | Let (x,m,n) ->
        let mTy = infer d g m
        let g' = g @ [(x, mTy)]
        infer d g' n
    | LetCast (x,j,y,m) ->
        let yTy = varLkup y
        let yI  = getIface yTy
        if Type.subtype d yI j || Type.subtype d j yI then
          let g' = g @ [x, Obj j]
          infer d g' m
        else
          raise (TypeError (sprintf "Invalid cast %O" t))
    | LetCl (x,y,mth,ns,n) ->
        let yTy = varLkup y
        let argTys,resTy =
          let i = getIface yTy 
          Type.ofMeth d i mth
        do List.iter2 (check d g) ns (List.map fromTy argTys)
        let g' = g @ [x, (fromTy resTy)]
        infer d g' n
    | While (m,n) ->
        do check d g m Int
        do check d g n Void
        Void
    | New (z,i,ms) ->
        let iMths  = ITbl.methods d i
        let iMths' = List.map (fun (mid,argtys,rty) -> (mid, List.map fromTy argtys, fromTy rty)) iMths
        let findMth (mth: MethId) (ms: List<MethSpec>) : MethSpec =
          match List.tryFind (fun (m: MethSpec) -> m.Name = mth) ms with
          | None   -> raise (TypeError (sprintf "Method %O in table for %O but not implemented in %O." mth i t))
          | Some s -> s
        List.iter (fun (mth,tys,ty) -> checkMth d g i (tys,ty) (findMth mth ms)) iMths'
        Obj i
    | Null -> NullTy (newTyVar ())
  try unify ety ty with
  | UnifyError -> raise (TypeError (sprintf "Could not unify Type %O and %O for %O." (zonk ety) (zonk ty) t))

and private checkMth (d: ITbl) (g: ETyEnv) (i: IntId) (aTys: List<ETy>, rTy: ETy) (s: MethSpec) : Unit =
  let g' = g @ List.map2 (fun x y -> (x,y)) s.Vars aTys
  check d g' s.Body rTy

and private infer (d: ITbl) (g: ETyEnv) (t: Term) : ETy =
  let var = Var (newTyVar ())
  do check d g t var
  var

/// Given an interface table d, a type environment g and a term t,
/// returns an extended type ety such that d,g |- t : ety or
/// raises TypeError if no such type exists.
let inferETy (d: ITbl) (g: TyEnv) (t: Term) : ETy =
  let g' = List.map (fun (x,ty) -> (x,fromTy ty)) g
  infer d g' t

/// Given an interface table d, a type environment g and a term t,
/// checks that 
//let checkFragment (d: ITbl) (g: TyEnv) (t: Term) (ty: Ty) : Unit =
//
//  let rec cf t =
//    match t with
//    | BVar x -> 
//        let ty = TyEnv.lookup x g
//        if not (Type.isB d ty) then raise (TypeError (sprintf "Variable %O has type %O not in the B fragment." t ty))
//    | Num _ -> ()
//    | Skip -> ()
//    | Plus (m,n) ->
//        do cf m
//        do checkFragment d g n
//    | Eq (m,n) -> 
//        do checkFragment d g m
//        do checkFragment d g n
//    | VEq (x,y) ->
//        let tyx = TyEnv.lookup x g
//        let tyy = TyEnv.lookup y g
//        if not (Type.isL d tyx) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." x tyx))
//        if not (Type.isL d tyy) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." y tyy))
//    | Seq (m,n) ->
//        do checkFragment d g m
//        do checkFragment d g n
//    | Cond (m,n,p) ->
//        do checkFragment d g m
//        do checkFragment d g n
//        do checkFragment d g p
//    | Assn (m,f,n) ->
//        do checkFragment d g m
//        do checkFragment d g n
//    | Fld (m,f) ->
//        do checkFragment d g m
//    | VFld (x,f) ->
//        let tyx = TyEnv.lookup x g
//        if not (Type.isL d tyx) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." x tyx))
//    | Call (m,mth,ns) ->
//        do checkFragment d g m
//        do List.iter (checkFragment d g) ns
//    | Cast (j,m) ->
//        do checkFragment d g m
//    | Let (x,m,n) ->
//        let tyx = TyEnv.lookup x g
//        do checkFragment d g m
//        do checkFragment d g n
//        if not (Type.isL d tyx) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." x tyx))
//    | LetCast (x,j,y,m) ->
//        let tyx = TyEnv.lookup x g
//        let tyy = TyEnv.lookup y g
//        if not (Type.isL d tyx) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." x tyx))
//        if not (Type.isL d tyy) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." y tyy))
//        do checkFragment d g m
//    | LetCl (x,y,mth,ns,n) ->
//        let tyx = TyEnv.lookup x g
//        let tyy = TyEnv.lookup y g
//        if not (Type.isL d tyx) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." x tyx))
//        if not (Type.isL d tyy) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." y tyy))
//        do List.iter (checkFragment d g) ns
//        do checkFragment d g n
//    | While (m,n) ->
//        do checkFragment d g m
//        do checkFragment d g n
//    | New (z,i,ms) ->
//        if not (Type.isL d (Iface i)) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." z i))
//        let checkMeth (m: MethSpec) =
//          let tys, ty = Type.ofMeth d i m.Name
//          let g' = g @ List.zip m.Vars tys
//          checkFragment d g' m.Body
//        do List.iter checkMeth ms
//    | Null -> ()