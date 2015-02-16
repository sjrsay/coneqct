namespace IMJEquiv

type Ident = String

type FldId = String
type MethId = String
type IntId = String

type RegId = Int32

exception TypeError of String

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

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module TyEnv =
  
  let lookup (x: Ident) (e: TyEnv) : Option<Ty> =
    // We deliberately look from the back of the list because there may be
    // two occurrences of the same identifier with the intention that
    // the later one shadows the former one.
    List.foldBack (fun (y,ty) opt -> match opt with Some _ -> opt | None -> if x = y then Some ty else None) e None

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module ITbl =
  
  let rec methods (t: ITbl) (i: IntId) : List<MethId * List<Ty> * Ty> =
    match Map.tryFind i t with
    | None -> failwith "Did not find interface %O in table %O." i t
    | Some tbd ->
        let m, ext = 
          match tbd with
          | Eqn m -> (m, [])
          | Ext (j, m) -> (m, methods t j)
        let ss = Map.fold (fun ss s dfn -> match dfn with IMth (tys,ty) -> (s,tys,ty)::ss | _ -> ss) [] m
        ext @ ss

  let rec fields (t: ITbl) (i: IntId) : List<FldId * Ty> =
    match Map.tryFind i t with
    | None -> failwith "Did not find interface %O in table %O." i t
    | Some tbd ->
        let m, ext = 
          match tbd with
          | Eqn m -> (m, [])
          | Ext (j, m) -> (m, fields t j)
        let ss = Map.fold (fun ss s dfn -> match dfn with IFld ty -> (s,ty)::ss | _ -> ss) [] m
        ext @ ss

  let rec isG (d: ITbl) (t: Ty) : Bool =
    match t with
    | Int | Void -> true
    | Iface i ->
        let flds = fields d i
        let mths = methods d i
        List.isEmpty mths && List.forall (isG d << snd) flds

  let rec isL (d: ITbl) (t: Ty) : Bool =
    match t with
    | Int | Void -> true
    | Iface i -> 
        let flds = fields d i
        let mths = methods d i
        let fldsAreG = List.forall (isG d << snd) flds
        let isGtoL (_,tys,ty) =
          List.forall (isG d) tys && isL d ty 
        let mthsAreGtoL = List.forall isGtoL mths
        fldsAreG && mthsAreGtoL

  let rec isR (d: ITbl) (t: Ty) : Bool =
    match t with
    | Int | Void -> true
    | Iface i ->
        let flds = fields d i
        let mths = methods d i
        let fldsAreG = List.forall (isG d << snd) flds
        let isLtoG (_,tys,ty) =
          List.forall (isL d) tys && isG d ty 
        let mthsAreLtoG = List.forall isLtoG mths
        fldsAreG && mthsAreLtoG

  let rec isB (d: ITbl) (t: Ty) : Bool =
    isL d t && isR d t

  let wellFormed (d: ITbl) : Unit =

    let rec wfTy (seen: Set<IntId>) (t: Ty) : Unit =
      match t with
      | Int 
      | Void -> ()
      | Iface i ->
          if Set.contains i seen then 
            raise (TypeError (sprintf "Recursive dependency in interface table."))
          else 
            match Map.tryFind i d with
            | None    -> raise (TypeError (sprintf "Definition of interface %O is missing." i))
            | Some df -> wf (Set.add i seen) df

    and wfIDfn (seen: Set<IntId>) (df: IDfn) : Unit =
      let tys = 
        match df with
        | IFld ty -> [ty]
        | IMth (tys,ty) -> ty::tys
      List.iter (wfTy seen) tys

    and wf (seen: Set<IntId>) (i: ITblDfn) : Unit =
      let m = 
        match i with
        | Eqn m      -> m
        | Ext (j, m) -> 
            if Set.contains j seen then
              raise (TypeError (sprintf "Recursive dependency in interface table."))
            else
              match Map.tryFind j d with
              | None -> raise (TypeError (sprintf "Definition of interface %O is missing." i))
              | Some df -> wf (Set.add j seen) df
              m
      Map.iter (fun _ df -> wfIDfn seen df) m

    Map.iter (fun k tbldf -> wf (set [k]) tbldf) d

    

module Types =
  
  let getPosInTyEnv (x: Ident) (e: TyEnv) : Int32 =
    List.findIndex (fun (y, _) -> x = y) e 

  let getTyfromTyEnv (x: Ident) (e: TyEnv) : Ty =
    snd (List.find (fun (y, _) -> x = y) e)

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

  let rec ofMeth (d: ITbl) (i: IntId) (mth: MethId) : (List<Ty> * Ty) =
    let foo (m: IDfnMap) : Option< (List<Ty>*Ty) > =
      match Map.tryFind mth m with
      | None -> None
      | Some (IFld _) -> failwith "Expected method."
      | Some (IMth (ins,out))  -> Some (ins,out)
    match d.[i] with
    | Eqn m -> Option.get (foo m)
    | Ext (j, m) ->
        match foo m with
        | None -> ofMeth d j mth
        | Some x -> x

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

