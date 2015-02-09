namespace IMJEquiv
open IMJEquiv

[<StructuredFormatDisplayAttribute("{Show}")>]
type Val =
  | VNum of Int32
  | VStar
  | VNul
  | VReg of RegId

  override x.ToString () : String =
    match x with
    | VNum n -> n.ToString()
    | VStar  -> "*"
    | VNul   -> "null"
    | VReg n -> n.ToString()

  member x.Show = x.ToString ()

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Val =

  let maxint = 2

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

  let defaultOfTy (ty: Ty) : Val =
    match ty with
    | Void    -> VStar
    | Int     -> VNum 0
    | Iface _ -> VNul
