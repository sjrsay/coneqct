﻿namespace IMJEquiv
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
      | VReg r -> 
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
      | VReg r -> Set.add r acc
      | _     -> acc
    let getOuterVals acc _ (_,m) =
      Map.fold getInnerVals acc m
    let cod = Map.fold getOuterVals Set.empty s
    (Map.domain s, cod)

  let supp (s: Store) : Set<RegId> =
    let dom, cod = splitSupp s
    Set.union dom cod

  /// Given a store `s` and a set of registers `rs`, `trim s rs` is
  /// the store `s@rs`, i.e. containing only those parts of `s` that
  /// are reachable from `rs`.
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

  let nextTypedReg (rs: Set<RegId * IntId>) : RegId =
    let n = ref 1
    while Set.exists (fun (r, _) -> r = !n) rs do
      n := !n + 1
    !n

  ///
  /// This is a private helper function for `stores` which follows this definition.
  ///
  /// Given an interface table `d`, a list of registers `rs` a list of fields `fs` and a store `s` and set of
  /// typed registers `s0Names` such that the following holds:
  ///
  ///   1. If `fs` is non-empty then `rs` is of the form `r'::rs'` and `r'` is in the domain of `s`, but
  ///      it is mapped to a field table which is missing entries for exactly fields in `fs`.
  ///   2. The intersection of `supp s` and `s0Names` is empty (mod types in the latter).
  ///
  /// then `vals d rs fs s s0'` is a list of all possible stores arising from, for each `r` in `rs` 
  /// mapping `r` to nondeterministically chosen field values in `s`.  
  ///
  /// For a field of type int, values range over `[0..Val.maxint]`.  For a field of interface type, values
  /// can be either: a fresh register id (not occurring in either `supp s` or `s0Names`), a register id 
  /// of the correct type already in `s` or a register id of the correct type from `s0Names`.
  ///
  /// NOTE: Constraint 2 is only for efficiency reasons, it ensures that the same register id cannot be
  /// chosen twice by being picked once from `s0Names` and once from `supp s`.  Hence, it allows combining 
  /// `supp s` and `s0Names` into a list rather than a set.
  ///
  let rec private vals (d: ITbl) (rs: List<RegId>) (fs: List<FldId>) (s: Store) (s0Names: Set<RegId * IntId>) : List<Store> =
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
                vals d rs' fs s' s0Names
        | f::fs' ->
            let acc = ref []
            let rIface = fst s.[r]
            match Types.ofFld d rIface f with
            | Ty.Int ->
                for x in [0..Val.maxint] do
                  let s' = Map.update r (fun (i, m) -> (i, Map.add f (VNum x) m)) s
                  let ss = vals d rs fs' s' s0Names
                  acc := List.append ss !acc
                !acc   
            | Ty.Void ->
                let s' = Map.update r (fun (i, m) -> (i, Map.add f VStar m)) s
                vals d rs fs' s' s0Names
            | Ty.Iface i ->
                let sTypedSupp = tySupp d s
                let sFilteredSupp = Set.fold (fun acc (r, j) -> if i = j then r :: acc else acc) [] sTypedSupp
                let s0'Filtered = Set.fold (fun acc (r, j) -> if i = j then r :: acc else acc) [] s0Names
                let fresh = nextTypedReg (Set.union sTypedSupp s0Names)
                let choices = fresh :: sFilteredSupp @ s0'Filtered
                for x in choices do
                  let s' = Map.update r (fun (i, m) -> (i, Map.add f (VReg x) m)) s
                  // We remove x from `s0Names` to ensure that `s0Names` and `supp s`
                  // are still disjoint according to constraint 2 and the note.
                  let s0Names' = Set.remove (x, i) s0Names  
                  let ss = vals d rs fs' s' s0Names'
                  acc := List.append ss !acc
                !acc

  /// Given an interface table `d`, an initial store `s0` and a set of registers `z`,
  /// `stores d s0 z` generates all possible stores `s` which have `dom(s)` including `z`
  /// and values taken from `*` for fields of type `void`, `[1..maxint]` for fields of
  /// type `int` and registers either drawn from `s0` or fresh.
  let stores (d: ITbl) (s0: Store) (z: Set<RegId>) : List<Store> =

    let rec storesAux (d: ITbl) (s: Store) (s0Names: Set<RegId * IntId>) (z: Set<RegId>) : List<Store> =
      let freeRegs = Set.toList (Set.difference z (Map.domain s))
      let acc = ref []
      match freeRegs with
      | []    -> [s]
      | r::rs ->
          let i, fs = fields s r
          let s' = Map.add r (i, Map.empty) s
          let spp = supp s'
          let s0Names' = Set.filter (fun (k, _) -> not (Set.contains k spp)) s0Names
          for s'' in vals d freeRegs fs s' s0Names' do
            let z' = supp s''
            if z = z' then acc := s'' :: !acc
            else acc := !acc @ storesAux d s'' s0Names' z'
          !acc

    storesAux d Map.empty (tySupp d s0) z

