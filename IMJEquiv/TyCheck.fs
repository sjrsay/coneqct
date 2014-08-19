module IMJEquiv.TyCheck
open IMJEquiv

#if __FALSE__ 

// Types extended by type variables
// for the purposes of unification.
type ETy =
  | Void
  | Int
  | Iface of IntId
  | Var of TyVar

and TyVar =
  {
    Inst : Ref<Option<ETy>>
  }


exception UnifyError
exception TypeError of Term * ETy * ETy

let newTyVar () : ETy =
  Var { Inst = ref None }

let private fromTy (t: Ty) : ETy =
  match t with
  | Ty.Void    -> Void
  | Ty.Int     -> Int
  | Ty.Iface i -> Iface i

let rec private zonk (t: ETy) : ETy =
  match t with 
  | Var x ->
      match !x.Inst with
      | None -> t
      | Some t' ->
          let t'' = zonk t'
          do x.Inst := Some t''
          t''
  | _ -> t

let rec unify (t1: ETy) (t2: ETy) : Unit =
  match t1, t2 with
  | _, _ when t1 = t2 -> ()
  | Var x, _ -> unifyVar x t2
  | _, Var y -> unifyVar y t1
  | _, _  -> raise UnifyError

and unifyVar (tv: TyVar) (t: ETy) : Unit =
  match !tv.Inst with
  | None -> unifyUnboundVar tv t
  | Some t' -> unify t' t

and unifyUnboundVar (tv: TyVar) (t: ETy) : Unit =
  match t with
  | Var x -> 
      match !x.Inst with
      | None -> tv.Inst := Some t
      | Some t' -> unify (Var tv) (zonk t')
  | _ ->
      tv.Inst := Some t

let rec check (env: TyEnv) (tbl: ITbl) (t: Term) (ty: ETy) : Unit =
  let ety =
    match t with
    | BVar x -> env.[x]
    | Num _  -> Int
    | Skip   -> Void
    | Plus (m,n) ->
        do check env tbl m Int
        do check env tbl n Int
        Int
    | Eq (m,n) ->
        let mTy = infer env tbl m
        do check env tbl n mTy
        mTy
    | VEq (x,y) ->
        let xTy = env.[x]
        let yTy = env.[y]
        try unify xTy yTy with
        | UnifyError -> raise (TypeError t xTy yTy)
    | Seq (m,n) ->
        do check env tbl m Void
        infer env tbl n
    | Cond (m,n,p) ->
        do check env tbl m Int
        let nTy = infer env tbl n
        check env tbl p nTy
        nTy
    | Assn (m,f,n) -> 
        let mTy = infer env tbl m
        let fTy = getFieldTy tbl mTy 
        check env tbl n fTy
        Void
    | Fld (m,f) ->
        let mTy = infer env tbl m
        getFieldTy tbl mTy f
    | VFld (x,f) ->
        let xTy = env.[x]
        getFieldTy tbl xTy f
    | Call (m,mth,ns) ->
        let mTy = infer env tbl m
        let argTys, resTy = getMethTy tbl mTy mth
        do List.iter2 (check env tbl) ns argTys
        resTy
    | Cast (j,m) ->
        let mTy = infer env tbl m
        if subtype tbl mTy j || subtype tbl j mTy then
          Iface j
        else
          raise (TypeError ...)
    | Let (x,m,n) ->
        let mTy = infer env tbl m
        let env' = Map.add x mTy env
        infer env' tbl n
    | LetCast (x,j,y,m) ->
        let yTy = env.[y]
        if subtype tbl yTy j || subtype tbl j yTy then
          let env' = Map.add x (Iface j) env
          infer env' tbl m
        else
          raise (TypeError ...)
    | LetCl (x,y,mth,ns,n) ->
        let yTy = env.[y]
        let argTys, resTy = getMethTy tbl yTy mth
        do List.iter2 (check env tbl) ns argTys
        let env' = Map.add x resTy env
        infer env' tbl n
    | While (m,n) ->
        do check env tbl m Int
        do check env tbl n Void
        Void
    | New (z,i,ms) ->
        let mthTys = 
    | Null -> 
  try unify ety ty with
  | UnifyError -> raise (TypeError (t, zonk ety, zonk ty))

and infer (env: TyEnv) (tbl: ITbl) (t: Term) : ETy =
  let var = newTyVar ()
  do check env tbl t var
  var

#endif 