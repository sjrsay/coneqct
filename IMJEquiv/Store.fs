namespace IMJEquiv

type Store =
  Map<RegId, IntId * Map<FldId, Val>>

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Store = 
  
  /// Given a symbolic store s, a register id k and a value v,
  /// such that s contains a register k which contains a field f,
  /// returns the store s but with f now mapped to v.
  let update (s: Store) (k: RegId) (f: FldId) (v: Val) : Store =
    let upd (i, m) =
      let newMap = 
        Map.update f (fun _ -> v) m
      (i, newMap)
    Map.update k upd s

  /// Given a permutation p of register ids and a store s,
  /// returns s but with those register ids stored in fields 
  /// permuted by p.
  let postPermute (p: Perm<RegId>) (s: Store) : Store =
    let permuteFields (p: Perm<RegId>) (m: Map<FldId, Val>) =
      Map.map (fun _ v -> Val.permute p v) m
    Map.map (fun _ (i, v) ->  (i, permuteFields p v)) s

  /// Given an interface table d and a store s, returns
  /// the typed support of s.
  let tySupp (d: ITbl) (s: Store) : Set<RegId * IntId> =
    let getInnerVals i acc f v =
      match v with
      | VReg r -> 
          let j = Type.toInterface (Type.ofFld d i f)
          Set.add (r, j) acc
      | _     -> acc
    let getOuterVals acc r (i,m) =
      Map.fold (getInnerVals i) (Set.add (r, i) acc) m
    Map.fold getOuterVals Set.empty s

  /// Given a store s, returns the pair of
  /// sets of registers (xs, ys), where xs is just
  /// the domain of s and ys is all those registers
  /// that occur in values stored in fields that are in
  /// the codomain of s.
  let splitSupp (s: Store) : Set<RegId> * Set<RegId> =
    let getInnerVals acc f v =
      match v with
      | VReg r -> Set.add r acc
      | _     -> acc
    let getOuterVals acc _ (_,m) =
      Map.fold getInnerVals acc m
    let cod = Map.fold getOuterVals Set.empty s
    (Map.domain s, cod)

  /// Given a store s, returns its support.
  let supp (s: Store) : Set<RegId> =
    let dom, cod = splitSupp s
    Set.union dom cod

  /// Given a store s and a set of registers rs, trim s rs is
  /// the store s@rs, i.e. containing only those parts of s that
  /// are reachable from rs.
  let trim (s: Store) (rs: Set<RegId>) : Store =
    let rec fix rs =
      let s' =
        Map.filter (fun r _ -> Set.contains r rs) s
      let newrs = Set.union (supp s') rs
      if newrs = rs then rs else fix newrs
    let supp = fix rs
    Map.filter (fun r _ -> Set.contains r supp) s

  /// Given a set of register ids rs returns
  /// the smallest register id fresh for rs.
  let nextReg (rs: Set<RegId>) : RegId =
    let n = ref 1
    while Set.contains !n rs do
      n := !n + 1
    !n

  /// Given a natural i and a set of register ids rs,
  /// returns the i smallest register ids fresh for rs.
  let rec nextiReg (i: Int32) (rs: Set<RegId>) : Set<RegId> =
    if i=0 then 
      Set.empty 
    else 
      let r = nextReg rs
      Set.add r (nextiReg (i-1) (Set.add r rs))

  /// Given a set of typed register ids rs, returns the 
  /// smallest register id that is fresh for the ids in rs.
  let nextTypedReg (rs: Set<RegId * IntId>) : RegId =
    let n = ref 1
    while Set.exists (fun (r, _) -> r = !n) rs do
      n := !n + 1
    !n

  /// Given an interface table d and an interface id i,
  /// returns a mapping from each field f:T of i according
  /// to d, to the default value of type T.
  let mkDefaultObj (d: ITbl) (i: IntId) : Map<FldId,Val> =
    let tyFlds = ITbl.fields d i
    let doField m (f, ty) =
      Map.add f (Val.defaultOfTy ty) m
    List.fold doField Map.empty tyFlds

  /// Given a store `s` and register id `r` such that
  /// `r` is in `dom(s)`, `tyOfReg s r` is the interface
  /// type of `r` according to `s`.
  let tyOfReg (s: Store) (r: RegId) : IntId =
    match Map.tryFind r s with
    | None -> failwith "Expected register %A in domain of store %A." r s
    | Some (i, _) -> i

  /// 
  /// This is a private helper function for `stores` which follows this definition.
  ///
  /// Given an integer `n`, an interface table `d`, a list of registers `rs` a list of fields `fs` 
  /// and a store `s` and set of typed registers `s0Names` such that the following holds:
  ///
  ///   1. If `fs` is non-empty then `rs` is of the form `r'::rs'` and `r'` is in the domain of `s`, but
  ///      it is mapped to a field table which is missing entries for exactly fields in `fs`.
  ///   2. The intersection of `supp s` and `s0Names` is empty (mod types in the latter).
  ///
  /// then `vals n d rs fs s s0'` is a list of all possible stores arising from, for each `r` in `rs` 
  /// mapping `r` to nondeterministically chosen field values in `s` with integers ranging from `0` to `n`.  
  ///
  /// For a field of type int, values range over `[0..n]`.  For a field of interface type, values
  /// can be either: a fresh register id (not occurring in either `supp s` or `s0Names`), a register id 
  /// of the correct type already in `s` or a register id of the correct type from `s0Names`.
  ///
  /// NOTE: Constraint 2 is only for efficiency reasons, it ensures that the same register id cannot be
  /// chosen twice by being picked once from `s0Names` and once from `supp s`.  Hence, it allows combining 
  /// `supp s` and `s0Names` into a list rather than a set.
  ///
  let rec private vals (n: Int) (d: ITbl) (rs: List<RegId * IntId>) (fs: List<FldId * Ty>) (s: Store) (s0Names: Set<RegId * IntId>) : List<Store> =
    match rs with
    | [] -> [s]
    | (r,i)::rs' ->
        match fs with
        | [] -> 
            match rs' with
            | [] -> [s]
            | (r',j)::rs'' ->
                let fs = ITbl.fields d j
                let s' = Map.add r' (j, Map.empty) s
                vals n d rs' fs s' s0Names
        | (f, ty)::fs' ->
            let acc = ref []
            match ty with
            | Ty.Int ->
                for x in [0..n] do
                  let s' = Map.update r (fun (i, m) -> (i, Map.add f (VNum x) m)) s
                  let ss = vals n d rs fs' s' s0Names
                  acc := List.append ss !acc
                !acc   
            | Ty.Void ->
                let s' = Map.update r (fun (i, m) -> (i, Map.add f VStar m)) s
                vals n d rs fs' s' s0Names
            | Ty.Iface i ->
                let sTypedSupp = tySupp d s
                let sFilteredSupp = Set.fold (fun acc (r, j) -> if i = j then r :: acc else acc) [] sTypedSupp
                let s0'Filtered = Set.fold (fun acc (r, j) -> if i = j then r :: acc else acc) [] s0Names
                let fresh = nextTypedReg (Set.unionMany [sTypedSupp; s0Names; set rs])
                let choices = fresh :: sFilteredSupp @ s0'Filtered
                for x in choices do
                  let s' = Map.update r (fun (i, m) -> (i, Map.add f (VReg x) m)) s
                  // We remove x from `s0Names` to ensure that `s0Names` and `supp s`
                  // are still disjoint according to constraint 2 and the note.
                  let s0Names' = Set.remove (x, i) s0Names  
                  let ss = vals n d rs fs' s' s0Names'
                  acc := List.append ss !acc
                // One final choice is to assign `null` to the field
                let s' = Map.update r (fun (i, m) -> (i, Map.add f VNul m)) s
                let ss = vals n d rs fs' s' s0Names
                acc := List.append ss !acc
                !acc

  ///
  /// Given an interface table `d`, an initial store `s0` and a set of registers `z`,
  /// returns all possible stores `s` which have `dom(s)` including `z` 
  /// and values taken from `{*}` for fields of type `void`, `{1..maxint}` for fields of
  /// type `int` and registers either drawn from `s0` or fresh.
  ///
  let stores (d: ITbl) (s0: Set<RegId * IntId>) (z: Set<RegId * IntId>) : List<Store> =

    let rec storesAux (d: ITbl) (s: Store) (s0Names: Set<RegId * IntId>) (z: Set<RegId * IntId>) : List<Store> =
      let sDom = Map.fold (fun dom k (i,_) -> Set.add (k, i) dom) Set.empty s
      let freeRegs = Set.toList (Set.difference z sDom)
      let acc = ref []
      match freeRegs with
      | []    -> [s]
      | (r,i)::rs ->
          let fs = ITbl.fields d i
          let s' = Map.add r (i, Map.empty) s
          let spp = supp s'
          let s0Names' = Set.filter (fun (k, _) -> not (Set.contains k spp)) s0Names
          for s'' in vals Val.maxint d freeRegs fs s' s0Names' do
            let z' = tySupp d s''
            if z = z' then acc := s'' :: !acc
            else acc := !acc @ storesAux d s'' s0Names' z'
          !acc

    storesAux d Map.empty s0 z

   
   
  /// Given a set of registers fxd, and stores s and t, returns Some p just in 
  /// case there is some permutation of register ids fixing fxd such that p(s) = t
  /// and None otherwise.  
  let alphaEq (fxd: Set<RegId>) (s: Store) (t: Store) : Option<Perm<RegId>> =
    
    let rec checkField (v: Val) (w: Val) (p: Perm<RegId>) : Option<Perm<RegId>> =
      match v, w with
      | VNum n, VNum m -> if n = m then Some p else None
      | VStar, VStar   -> Some p
      | VNul, VNul     -> Some p
      | VReg a, VReg b -> aeq (a, b) p 
      | _, _           -> None

    and aeq (l: RegId, r: RegId) (p: Perm<RegId>) =
      match Map.tryFind l p with
      | Some r' -> if r = r' then Some p else None
      | None ->
          let codp = Map.codomain p
          if Set.contains r codp then
            None
          else
            let p' = Map.add l r p
            match Map.tryFind l s, Map.tryFind r t with
            | None, None -> Some p
            | Some (lty, lflds), Some (rty, rflds) ->
                if lty = rty then
                  Map.fold (fun popt f v -> match popt with Some p' -> checkField v rflds.[f] p' | None -> None) (Some p') lflds
                else
                  None
            | _, _ -> None

    Set.fold (fun popt r -> match popt with Some p -> aeq (r, r) p | None -> None) (Some Map.empty) fxd   

  /// Given a set of register ids fixd, a store s and a list of stores ss such that there 
  /// is some store s', permutation p such that s' in ss and alphaEq fixd s s' = p, returns (s', p)
  let findWithWitness (fixd: Set<RegId>) (s: Store) (ss: List<Store>) : Store * Perm<RegId> =
    let folder opt s' =
      match opt with 
      | Some x -> Some x
      | None    ->
          match alphaEq fixd s s' with
          | None       -> None
          | Some p'    -> Some (s', p')

    match List.fold folder None ss with
    | None -> failwith "Expected to find alpha-equivalent store"
    | Some p -> p

   
  /// Given an interface table d, a type environment g and a list of moves (tuple move) ms,
  /// returns a list of all the possible initial symbolic stores for ms wrt d and g.
  let fromMoves (d: ITbl) (g: TyEnv) (ms: List<Move>) : List<Store> =
    let tyspp = List.fold2 (fun s m (_,ty) -> match m, ty with ValM (VReg r), Iface i -> Set.add (r,i) s | _ -> s) Set.empty ms g
    stores d Set.empty tyspp
