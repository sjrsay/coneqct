namespace IMJEquiv

type Ident = String

type FldId = String
type MethId = String
type IntId = String

[<StructuredFormatDisplayAttribute("{Show}")>]
type Ty = 
  | Void
  | Int
  | Iface of IntId

  member t.Show : String =
    t.ToString ()

  override t.ToString () : String =
    match t with
    | Void -> "void"
    | Int -> "int"
    | Iface i -> i

type IDfn =
  | IFld of Ty
  | IMth of List<Ty> * Ty

type IDfnMap = Map<String, IDfn>

/// The type `ITblDfn' describes the kinds of
/// identities in the interface table:
/// `Eqn d` is a straightforward definition by `d`
/// `Ext J d` is an extension of the definition of `J`
/// by those items defined in `d`.
type ITblDfn =
  | Eqn of IDfnMap
  | Ext of IntId * IDfnMap

type ITbl = Map<IntId, ITblDfn>

module Types =
  
  /// Given an interface table `d` and two interface idents `i`
  /// and `j`, `subtype d i j` is `true` just if `i` is a subtype
  /// (i.e. stronger than) `j` according to `d` and is `false` o/w.
  let rec subtype (d: ITbl) (i: IntId) (j: IntId) : Bool =
    if i = j then 
      true 
    else
      match Map.tryFind i d with
      | None -> false
      | Some dfn ->
          match dfn with
          | Eqn _      -> false
          | Ext (k, _) -> subtype d k j

