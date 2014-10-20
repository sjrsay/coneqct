namespace IMJEquiv
open IMJEquiv

type Move = 
  | ValM of Val
  | Call of RegId * MethId * List<Val>
  | Ret of RegId * MethId * Val


[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Move =

  let rec supp (m: Move) : Set<RegId> =
    match m with
    | ValM v -> Val.supp v
    | Call (r,mth,vs) -> 
        List.fold (fun rvs v -> Set.union (Val.supp v) rvs) (Set.singleton r) vs
    | Ret (r,mth,v) ->
        Set.add r (Val.supp v)
