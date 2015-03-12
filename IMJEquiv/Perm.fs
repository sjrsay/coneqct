namespace IMJEquiv

/// The type of finite permutations implemented as finite maps.
/// Hence, as a type, Perm<'a>, admits many inhabitants that
/// are not actually permutations.
type Perm<'a> when 'a : comparison = Map<'a,'a>

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Perm =
  
  /// Given a sets of register ids fxd, a and b, 
  /// such that a + fxd = b + fxd = D (say), returns all permutations on D that
  /// fix elements from fxd.
  let allPerms (fxd: Set<RegId>) (a: Set<RegId>) (b: Set<RegId>) : List<Perm<RegId>> =
    
    // Here, p is the accumulated permutation
    let rec mkPerms u v (p: Perm<RegId>) : List<Perm<RegId>> =
      match u with
      | [] -> []
      | x::xs ->
          Set.fold (fun xss y -> mkPerms xs (Set.remove y v) (Map.add x y p) @ xss) [] v

    let a' = Set.difference a fxd
    let b' = Set.difference b fxd
    let p = Set.fold (fun p x -> Map.add x x p) Map.empty fxd
    mkPerms (Set.toList a') b' p

  /// Given sets of register ids fxd, a and b, such that a + fxd = b + fxd = D (say);
  /// returns all partial permutations on D (i.e. all partial injections) that at least
  /// fix all the elements of fxd.
  let allPartialPerms (fxd: Set<RegId>) (a: Set<RegId>) (b: Set<RegId>) : List<Perm<RegId>> =
    
    let rec mkPartialPerms u v (p: Perm<RegId>) : List<Perm<RegId>> =
      match u with
      | [] -> [p]
      | x::xs ->
          // Either map x from u to each possible y from v...
          let xtoys = Set.fold (fun xss y -> mkPartialPerms xs (Set.remove y v) (Map.add x y p) @ xss) [] v
          // ...or don't...
          let skipxs = mkPartialPerms xs v p
          // ...and take both possibilities.
          skipxs @ xtoys

    let a' = Set.difference a fxd
    let b' = Set.difference b fxd
    let p = Set.fold (fun p x -> Map.add x x p) Map.empty fxd
    mkPartialPerms (Set.toList a') b' p
