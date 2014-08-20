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

type TyEnv = List<Ident * Ty>

module Types =
  
  let getPosInTyEnv (x: Ident) (e: TyEnv) : Int32 =
    List.findIndex (fun (y, _) -> x = y) e 

  /// The constant `varInt` is the VarInt interface,
  /// i.e. `{ val : int }`
  let varInt =
    Eqn (Map.singleton "val" (IFld Int))

  let rec ofFld (d: ITbl) (i: IntId) (f: FldId) : Ty =
    let foo (m: IDfnMap) : Option<Ty> =
      match Map.tryFind f m with
      | None -> None
      | Some (IFld ty) -> Some ty
      | Some (IMth _)  -> failwith "Expected field."
    match d.[i] with
    | Eqn m -> Option.get (foo m)
    | Ext (j, m) ->
        match foo m with
        | None -> ofFld d j f
        | Some ty -> ty

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

