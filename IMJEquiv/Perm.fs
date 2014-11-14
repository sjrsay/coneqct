namespace IMJEquiv
open IMJEquiv

type Perm<'a> when 'a : comparison = Map<'a,'a>

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Perm =
  
  let preApply (m: Map<'a,'b>) (p: Perm<'a>) : Map<'a,'b> =
    Map.fold (fun m' k v -> Map.add p.[k] v m') Map.empty m

  let allPerms (fxd: Set<RegId>) (a: Set<RegId>) (b: Set<RegId>) : List<Perm<RegId>> =
    
    let rec mkPerms u v (p: Perm<RegId>) : List<Perm<RegId>> =
      match u with
      | [] -> []
      | x::xs ->
          Set.fold (fun xss y -> mkPerms xs (Set.remove y v) (Map.add x y p) @ xss) [] v

    let a' = Set.difference a fxd
    let b' = Set.difference b fxd
    let p = Set.fold (fun p x -> Map.add x x p) Map.empty fxd
    mkPerms (Set.toList a') b' p

  let allPartialPerms (fxd: Set<RegId>) (a: Set<RegId>) (b: Set<RegId>) : List<Perm<RegId>> =
    
    let rec mkPartialPerms u v (p: Perm<RegId>) : List<Perm<RegId>> =
      match u with
      | [] -> []
      | x::xs ->
          let xtoys = Set.fold (fun xss y -> mkPartialPerms xs (Set.remove y v) (Map.add x y p) @ xss) [] v
          let skipxs = mkPartialPerms xs v p
          skipxs @ xtoys

    let a' = Set.difference a fxd
    let b' = Set.difference b fxd
    let p = Set.fold (fun p x -> Map.add x x p) Map.empty fxd
    mkPartialPerms (Set.toList a') b' p

  let extendPartial (p: Perm<RegId>) (remDom: List<RegId>) (remCod: List<RegId>) : Perm<RegId> =
    List.fold2 (fun p x y -> Map.add x y p) p remDom remCod