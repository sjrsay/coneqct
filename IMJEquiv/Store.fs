namespace IMJEquiv
open IMJEquiv

type Store =
  Map<RegId, IntId * Map<FldId, Val>>

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Store = 
  
  /// Given a symbolic store `s`, a register id `k` and a value `v`,
  /// such that `s` contains a register `k` which contains a field `f`,
  /// `update s k v` is the store `s` but with `f` now mapped to `v`.
  let update (s: Store) (k: RegId) (f: FldId) (v: Val) : Store =
    let upd (i, m) =
      let newMap = 
        Map.update f (fun _ -> v) m
      (i, newMap)
    Map.update k upd s


  let private permuteFields (p: Perm<RegId>) (m: Map<FldId, Val>) : Map<FldId, Val> =
    Map.map (fun _ v -> Val.permute p v) m

  let postPermute (p: Perm<RegId>) (s: Store) : Store =
    Map.map (fun _ (i, v) ->  (i, permuteFields p v)) s

  let tySupp (d: ITbl) (s: Store) : Set<RegId * IntId> =
    let getInnerVals i acc f v =
      match v with
      | Reg r -> 
          let (Iface j) = Types.ofFld d i f
          Set.add (r, j) acc
      | _     -> acc
    let getOuterVals acc r (i,m) =
      Map.fold (getInnerVals i) (Set.add (r, i) acc) m
    Map.fold getOuterVals Set.empty s

  /// Given a store `s`, `splitSupp s` is the pair of
  /// sets of registers `(xs, ys)`, where `xs` is just
  /// the domain of `s` and `ys` is all those registers
  /// that occur in values stored in fields that are in
  /// the codomain of `s`.
  let splitSupp (s: Store) : Set<RegId> * Set<RegId> =
    let getInnerVals acc f v =
      match v with
      | Reg r -> Set.add r acc
      | _     -> acc
    let getOuterVals acc _ (_,m) =
      Map.fold getInnerVals acc m
    let cod = Map.fold getOuterVals Set.empty s
    (Map.domain s, cod)

  let supp (s: Store) : Set<RegId> =
    let dom, cod = splitSupp s
    Set.union dom cod

  let trim (s: Store) (rs: Set<RegId>) : Store =
    let rec fix rs =
      let s' =
        Map.filter (fun r _ -> Set.contains r rs) s
      let newrs = Set.union (supp s') rs
      if newrs = rs then rs else fix newrs
    let supp = fix rs
    Map.filter (fun r _ -> Set.contains r supp) s

  let fields (s: Store) (r: RegId) : IntId * List<FldId> =
    let i, m = s.[r]
    (i, Map.domainList m)

  let nextReg (rs: Set<RegId>) : RegId =
    let n = ref 1
    while Set.contains !n rs do
      n := !n + 1
    !n

  let rec private vals (d: ITbl) (rs: List<RegId>) (fs: List<FldId>) (s: Store) (s0': Store) : List<Store> =
    match rs with
    | [] -> [s]
    | r::rs' ->
        match fs with
        | [] -> 
            match rs' with
            | [] -> [s]
            | r'::rs'' ->
                let i, fs = fields s r'
                let s' = Map.add r' (i, Map.empty) s
                vals d rs' fs s' s0'
        | f::fs' ->
            let acc = ref []
            let rIface = fst s.[r]
            match Types.ofFld d rIface f with
            | Ty.Int ->
                for x in [0..Val.maxint] do
                  let s' = Map.update r (fun (i, m) -> (i, Map.add f (Num x) m)) s
                  let ss = vals d rs fs' s' s0'
                  acc := List.append ss !acc
                !acc   
            | Ty.Void ->
                let s' = Map.update r (fun (i, m) -> (i, Map.add f Star m)) s
                vals d rs fs' s' s0'
            | Ty.Iface i ->
                let sTypedSupp = tySupp d s
                let s0'TypedSupp = tySupp d s0'
                let sFilteredSupp = Set.fold (fun acc (r, j) -> if i = j then r :: acc else acc) [] sTypedSupp
                let s0'FilteredSupp = Set.fold (fun acc (r, j) -> if i = j && Set.contains r (Map.domain s0') then r :: acc else acc) [] s0'TypedSupp
                let fresh = nextReg (Set.union (Set.map fst sTypedSupp) (Map.domain s0'))
                let choices = fresh :: sFilteredSupp @ s0'FilteredSupp
                for x in choices do
                  let s' = Map.update r (fun (i, m) -> (i, Map.add f (Reg x) m)) s
                  let s0'' = Map.remove x s0'  // Maybe this is just for efficiency
                  let ss = vals d rs fs' s' s0''
                  acc := List.append ss !acc
                !acc

  // s is an accumulator
  let rec stores (d: ITbl) (s: Store) (s0: Store) (z: Set<RegId>) : List<Store> =
    let freeRegs = Set.toList (Set.difference z (Map.domain s))
    let acc = ref []
    match freeRegs with
    | []    -> [s]
    | r::rs ->
        let i, fs = fields s r
        let s' = Map.add r (i, Map.empty) s
        let spp = supp s'
        let s0' = Map.filter (fun k _ -> not (Set.contains k spp)) s0
        for s'' in vals d freeRegs fs s' s0' do
          let z' = supp s''
          if z = z' then acc := s'' :: !acc
          else acc := !acc @ stores d s'' s0' z' // shouldn't this be just acc := stores d s'' s0' z'?
        !acc

