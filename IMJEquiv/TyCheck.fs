module IMJEquiv.TyCheck
open IMJEquiv

// Types extended by type variables
// for the purposes of unification.
//type ETy =
//  | Void
//  | Int
//  | Obj of EIface
//  | Var of TyVar
//
//and TyVar =
//  {
//    Inst : Ref<Option<ETy>>
//  }
//
//and EIface =
//  | Iface of IntId
//  | IVar of IfVar
//
//and IfVar =
//  {
//    Inst : Ref<Option<EIface>>
//  }
//
//type ETyEnv = List<Ident * ETy>
//
//exception UnifyError
//exception TypeError of Term * ETy * ETy
//
//let newTyVar () : ETy =
//  Var { Inst = ref None }
//
//let private fromTy (t: Ty) : ETy =
//  match t with
//  | Ty.Void    -> Void
//  | Ty.Int     -> Int
//  | Ty.Iface i -> Obj (Iface i)
//
//let rec private zonk (t: ETy) : ETy =
//  match t with 
//  | Var x ->
//      match !x.Inst with
//      | None -> t
//      | Some t' ->
//          let t'' = zonk t'
//          do x.Inst := Some t''
//          t''
//  | _ -> t
//
//let rec private zonkIface (u: EIface) : EIface =
//  match u with
//  | IVar x ->
//      match !x.Inst with
//      | None -> u
//      | Some u' ->
//          let v = zonkIface u'
//          do x.Inst := Some v
//          v
//  | _ -> u
//
//let rec unify (t1: ETy) (t2: ETy) : Unit =
//  match t1, t2 with 
//  | _, _ when t1 = t2 -> ()
//  | Var x, _ -> unifyVar x t2
//  | _, Var y -> unifyVar y t1
//  | Obj x, Obj y -> unifyObjs x y
//  | _, _  -> raise UnifyError
//
//and unifyObjs (u: EIface) (v: EIface) : Unit =
//  match u, v with
//  | Iface i, Iface j when i = j -> ()
//  | IVar x, _ -> unifyIfVar x v
//  | _, IVar y -> unifyIfVar y u
//  | _, _      -> raise UnifyError
//
//and unifyIfVar (iv: IfVar) (u: EIface) : Unit =
//  match !iv.Inst with
//  | None -> unifyUnboundIfVar iv u
//  | Some u' -> unifyObjs u' u
//
//and unifyUnboundIfVar (iv: IfVar) (u: EIface) : Unit =
//  match u with
//  | IVar x ->
//      match !x.Inst with
//      | None -> iv.Inst := Some u
//      | Some v -> unifyObjs (IVar iv) (zonkIface v)
//  | _ -> 
//      iv.Inst := Some u
//
//and unifyVar (tv: TyVar) (t: ETy) : Unit =
//  match !tv.Inst with
//  | None -> unifyUnboundVar tv t
//  | Some t' -> unify t' t
//
//and unifyUnboundVar (tv: TyVar) (t: ETy) : Unit =
//  match t with
//  | Var x -> 
//      match !x.Inst with
//      | None -> tv.Inst := Some t
//      | Some t' -> unify (Var tv) (zonk t')
//  | _ ->
//      tv.Inst := Some t
//
//let rec check (d: ITbl) (g: ETyEnv) (t: Term) (ty: ETy) : Unit =
//
//  let varLkup x =
//    match TyEnv.lookup x g with
//    | None -> failwith "Variable %O not in environment." x
//    | Some ty -> fromTy ty
//
//  // There must be a better way to do this
//  let getIface (t: ETy) : IntId =
//    match t with
//    | Obj ifc -> 
//        match zonkIface ifc with
//        | Iface i -> i
//        | _       -> failwith "Expected interface for method resolution but found %O." t
//    | _ -> failwith "Expected interface for method resolution but found %O." t
//
//  let ety: ETy =
//    match t with
//    | BVar x -> varLkup x    
//    | Num _  -> Int
//    | Skip   -> Void
//    | Plus (m,n) ->
//        do check d g m Int
//        do check d g n Int
//        Int
//    | Eq (m,n) ->
//        let mTy = infer d g m
//        do check d g n mTy
//        mTy
//    | VEq (x,y) ->
//        let xTy = varLkup x
//        let yTy = varLkup y
//        try unify xTy yTy with
//        | UnifyError -> raise (TypeError (t, xTy, yTy))
//        xTy
//    | Seq (m,n) ->
//        do check d g m Void
//        infer d g n
//    | Cond (m,n,p) ->
//        do check d g m Int
//        let nTy = infer d g n
//        check d g p nTy
//        nTy
//    | Assn (m,f,n) -> 
//        let mTy = infer d g m
//        let mI  = getIface mTy
//        let fTy = Types.ofFld d mI f
//        check d g n (fromTy fTy)
//        Void
//    | Fld (m,f) ->
//        let mTy = infer d g m
//        let mI  = getIface mTy
//        fromTy (Types.ofFld d mI f)
//    | VFld (x,f) ->
//        let xTy = varLkup x
//        let xI  = getIface xTy
//        fromTy (Types.ofFld d xI f)
//    | Call (m,mth,ns) ->
//        let mTy = infer d g m
//        let mI  = getIface mTy
//        let argTys, resTy = Types.ofMeth d mI mth
//        do List.iter2 (fun n a -> check d g n (fromTy a)) ns argTys
//        fromTy resTy
//    | Cast (j,m) ->
//        let mTy = infer d g m
//        let mI  = getIface mTy
//        if Types.subtype d mI j || Types.subtype d j mI then
//          Obj (Iface j)
//        else
//          failwith "Error"
//    | Let (x,m,n) ->
//        let mTy = infer d g m
//        let g' = g @ [(x, mTy)]
//        infer d g' n
//    | LetCast (x,j,y,m) ->
//        let yTy = varLkup y
//        let yI  = getIface yTy
//        if Types.subtype d yI j || Types.subtype d j yI then
//          let g' = g @ x (Iface j) g
//          infer d g' m
//        else
//          failwith "Error"
//    | LetCl (x,y,mth,ns,n) ->
//        let yTy = varLkup y
//        let argTys, resTy = getMethTy d yTy mth
//        do List.iter2 (check d g) ns argTys
//        let g' = Map.add x resTy g
//        infer d g' n
//    | While (m,n) ->
//        do check d g m Int
//        do check d g n Void
//        Void
//    | New (z,i,ms) ->
//        let iMths = ITbl.methods d i
//        let findMth (mth: MethId) (ms: List<MethSpec>) : MethSpec =
//          match List.tryFind (fun (m: MethSpec) -> m.Name = mth) ms with
//          | None   -> failwith "Method %O in table for %O but not implemented in %O." mth i t
//          | Some s -> s
//        List.iter (fun (mth,tys,ty) -> checkMth d g i (tys,ty) (findMth mth ms)) iMths
//        Obj (Iface i)
//    | Null -> Obj (IVar { Inst = ref None })
//  try unify ety ty with
//  | UnifyError -> raise (TypeError (t, zonk ety, zonk ty))
//
//and checkMth (d: ITbl) (g: TyEnv) (i: IntId) (aTys: List<Ty>, rTy: Ty) (s: MethSpec) : Unit =
//  let g' = g @ List.map2 (fun x y -> (x,y)) s.Vars aTys
//  check d g' s.Body (fromTy rTy)
//
//and infer (d: ITbl) (g: TyEnv) (t: Term) : ETy =
//  let var = newTyVar ()
//  do check d g t var
//  var
