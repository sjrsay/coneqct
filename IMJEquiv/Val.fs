namespace IMJEquiv
open IMJEquiv

type RegId = Int32

type Val =
  | Num of Int32
  | Star
  | Nul
  | Reg of RegId

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Val =

  let maxint = 5

  let supp (v: Val) : Set<RegId> =
    match v with
    | Num _ 
    | Star 
    | Nul    -> Set.empty
    | Reg r  -> Set.singleton r 

  let permute (p: Perm<RegId>) (v: Val) : Val =
    match v with
    | Reg r -> Reg p.[r]
    | _     -> v