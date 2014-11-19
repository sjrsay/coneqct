namespace IMJEquiv
open IMJEquiv

[<StructuredFormatDisplay("{Show}")>]
type Move = 
  | ValM of Val
  | Call of RegId * MethId * List<Val>
  | Ret of RegId * MethId * Val

  override x.ToString () =
    match x with
    | ValM v -> v.ToString ()
    | Call (r, mth, vs) -> sprintf "call %d.%s(%s)" r mth (List.toStringWithDelims "" "," "" vs)
    | Ret (r, mth, v) -> sprintf "ret %d.%s(%O)" r mth v

  member x.Show = x.ToString ()

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Move =

  let rec supp (m: Move) : Set<RegId> =
    match m with
    | ValM v -> Val.supp v
    | Call (r,mth,vs) -> 
        List.fold (fun rvs v -> Set.union (Val.supp v) rvs) (Set.singleton r) vs
    | Ret (r,mth,v) ->
        Set.add r (Val.supp v)
