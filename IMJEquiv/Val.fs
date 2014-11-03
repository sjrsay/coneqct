namespace IMJEquiv
open IMJEquiv

type RegId = Int32

type Val =
  | VNum of Int32
  | VStar
  | VNul
  | VReg of RegId

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Val =

  let maxint = 5

  let supp (v: Val) : Set<RegId> =
    match v with
    | VNum _ 
    | VStar 
    | VNul    -> Set.empty
    | VReg r  -> Set.singleton r 

  let permute (p: Perm<RegId>) (v: Val) : Val =
    match v with
    | VReg r -> VReg p.[r]
    | _      -> v