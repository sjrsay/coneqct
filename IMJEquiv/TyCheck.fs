module IMJEquiv.TyCheck
open IMJEquiv

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

and TyVar =
  {
    Name : Int
    Inst : Ref<Option<ETy>>
  }

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

let private tyVarNum = ref 0
let newTyVar () : TyVar =
  do incr tyVarNum
  { Inst = ref None; Name = !tyVarNum }

let private lookup (x: Ident) (e: ETyEnv) : Option<ETy> =
  List.foldBack (fun (y,ty) opt -> match opt with Some _ -> opt | None -> if x = y then Some ty else None) e None

let private fromTy (t: Ty) : ETy =
  match t with
  | Ty.Void    -> Void
  | Ty.Int     -> Int
  | Ty.Iface i -> Obj i

let rec private zonk (t: ETy) : ETy =
  t.Zonk ()

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

and unifyVar (tv: TyVar) (t: ETy) : Unit =
  match !tv.Inst with
  | None -> unifyUnboundVar tv t
  | Some t' -> unify t' t

and unifyUnboundVar (tv: TyVar) (t: ETy) : Unit =
  match t with
  | Var x -> 
      match !x.Inst with
      | None -> tv.Inst := Some t
      | Some t' -> unifyUnboundVar tv (zonk t')
  | _ ->
      tv.Inst := Some t

let rec private check (d: ITbl) (g: ETyEnv) (t: Term) (ty: ETy) : Unit =

  let varLkup x =
    match lookup x g with
    | None -> raise (TypeError (sprintf "Variable %O not declared in the context." x))
    | Some ty -> ty

  // There must be a better way to do this
  let getIface (t: ETy) : IntId =
    let t' = zonk t
    match t' with
    | Obj ifc -> ifc
    | _ -> raise (TypeError (sprintf "Expected interface for method resolution but found %O." t))

  let ety: ETy =
    match t with
    | BVar x -> varLkup x    
    | Num _  -> Int
    | Skip   -> Void
    | Plus (m,n) ->
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
        let fTy = Types.ofFld d mI f
        check d g n (fromTy fTy)
        Void
    | Fld (m,f) ->
        let mTy = infer d g m
        let mI  = getIface mTy
        fromTy (Types.ofFld d mI f)
    | VFld (x,f) ->
        let xTy = varLkup x
        let xI  = getIface xTy
        fromTy (Types.ofFld d xI f)
    | Call (m,mth,ns) ->
        let mTy = infer d g m
        let mI  = getIface mTy
        let argTys, resTy = Types.ofMeth d mI mth
        do List.iter2 (fun n a -> check d g n (fromTy a)) ns argTys
        fromTy resTy
    | Cast (j,m) ->
        let mTy = infer d g m
        let mI  = getIface mTy
        if Types.subtype d mI j || Types.subtype d j mI then
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
        if Types.subtype d yI j || Types.subtype d j yI then
          let g' = g @ [x, Obj j]
          infer d g' m
        else
          raise (TypeError (sprintf "Invalid cast %O" t))
    | LetCl (x,y,mth,ns,n) ->
        let yTy = varLkup y
        let argTys,resTy =
          let i = getIface yTy 
          Types.ofMeth d i mth
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
  | UnifyError -> raise (TypeError (sprintf "Could not unify types %O and %O for %O." (zonk ety) (zonk ty) t))

and private checkMth (d: ITbl) (g: ETyEnv) (i: IntId) (aTys: List<ETy>, rTy: ETy) (s: MethSpec) : Unit =
  let g' = g @ List.map2 (fun x y -> (x,y)) s.Vars aTys
  check d g' s.Body rTy

and private infer (d: ITbl) (g: ETyEnv) (t: Term) : ETy =
  let var = Var (newTyVar ())
  do check d g t var
  var

let inferETy (d: ITbl) (g: TyEnv) (t: Term) : ETy =
  let g' = List.map (fun (x,ty) -> (x,fromTy ty)) g
  infer d g' t

let rec checkFragment (d: ITbl) (g: TyEnv) (t: Term) : Unit =
  match t with
  | BVar x -> 
      let (Some ty) = TyEnv.lookup x g
      if not (ITbl.isB d ty) then raise (TypeError (sprintf "Variable %O has type %O not in the B fragment." t ty))
  | Num _ -> ()
  | Skip -> ()
  | Plus (m,n) ->
      do checkFragment d g m
      do checkFragment d g n
  | Eq (m,n) -> 
      do checkFragment d g m
      do checkFragment d g n
  | VEq (x,y) ->
      let (Some tyx) = TyEnv.lookup x g
      let (Some tyy) = TyEnv.lookup y g
      if not (ITbl.isL d tyx) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." x tyx))
      if not (ITbl.isL d tyy) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." y tyy))
  | Seq (m,n) ->
      do checkFragment d g m
      do checkFragment d g n
  | Cond (m,n,p) ->
      do checkFragment d g m
      do checkFragment d g n
      do checkFragment d g p
  | Assn (m,f,n) ->
      do checkFragment d g m
      do checkFragment d g n
  | Fld (m,f) ->
      do checkFragment d g m
  | VFld (x,f) ->
      let (Some tyx) = TyEnv.lookup x g
      if not (ITbl.isL d tyx) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." x tyx))
  | Call (m,mth,ns) ->
      do checkFragment d g m
      do List.iter (checkFragment d g) ns
  | Cast (j,m) ->
      do checkFragment d g m
  | Let (x,m,n) ->
      let (Some tyx) = TyEnv.lookup x g
      do checkFragment d g m
      do checkFragment d g n
      if not (ITbl.isL d tyx) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." x tyx))
  | LetCast (x,j,y,m) ->
      let (Some tyx) = TyEnv.lookup x g
      let (Some tyy) = TyEnv.lookup y g
      if not (ITbl.isL d tyx) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." x tyx))
      if not (ITbl.isL d tyy) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." y tyy))
      do checkFragment d g m
  | LetCl (x,y,mth,ns,n) ->
      let (Some tyx) = TyEnv.lookup x g
      let (Some tyy) = TyEnv.lookup y g
      if not (ITbl.isL d tyx) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." x tyx))
      if not (ITbl.isL d tyy) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." y tyy))
      do List.iter (checkFragment d g) ns
      do checkFragment d g n
  | While (m,n) ->
      do checkFragment d g m
      do checkFragment d g n
  | New (z,i,ms) ->
      if not (ITbl.isL d (Iface i)) then raise (TypeError (sprintf "Variable %s has type %O not in the L fragment." z i))
      let checkMeth (m: MethSpec) =
        let tys, ty = Types.ofMeth d i m.Name
        let g' = g @ List.zip m.Vars tys
        checkFragment d g' m.Body
      do List.iter checkMeth ms
  | Null -> ()