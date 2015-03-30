namespace IMJEquiv

/// The basic identifiers that IMJ terms
/// are built from are just strings.  It
/// seems unlikely that instances will ever
/// be so large as to make this an efficiency
/// concern.
type Ident = String
type FldId = String
type MethId = String
type IntId = String

/// Register identifiers (indexes)
type RegId = Int32

/// Type errors
exception TypeError of String

/// Types in IMJ
type Ty = 
  | Void
  | Int
  | Iface of IntId

  override t.ToString () : String =
    match t with
    | Void -> "void"
    | Int -> "int"
    | Iface i -> i

/// The declared type of a method or field 
/// in an interface.
type IDfn =
  | IFld of Ty
  | IMth of List<Ty> * Ty

/// An interface defines a mapping from method and field
/// names to their declared types.
type IDfnMap = Map<String, IDfn>

/// The type `ITblDfn' describes the kinds of
/// identities in the interface table:
/// `Eqn d` is a straightforward definition by `d`
/// `Ext J d` is an extension of the definition of `J`
/// by those items defined in `d`.
type ITblDfn =
  | Eqn of IDfnMap
  | Ext of IntId * IDfnMap

/// Interface table
type ITbl = Map<IntId, ITblDfn>

/// Type environment
type TyEnv = List<Ident * Ty>

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module TyEnv =
  
  /// Given a variable x and a type environment [(x_0,ty_0);...;(x_n,ty_n)]
  /// where there is some i such that x_i = x, returns i.
  let index (x: Ident) (e: TyEnv) : Int32 =
    List.findIndex (fun (y, _) -> x = y) e 

  /// Given a variable x and a type environment [(x_0,ty_0);...;(x_n,ty_n)]
  /// where there is some i such that x_i = x, returns ty_i.
  let lookup (x: Ident) (e: TyEnv) : Ty =
    snd (List.find (fun (y, _) -> x = y) e)

  /// Given an ident x and a type environment [(x_0,ty_0);...;(x_n,ty_n)], 
  /// returns Some ty_i when x_i = x and None otherwise.
  let tryLookup (x: Ident) (e: TyEnv) : Option<Ty> =
    // We deliberately look from the back of the list because there may be
    // two occurrences of the same identifier with the intention that
    // the later one shadows the former one.
    List.foldBack (fun (y,ty) opt -> match opt with Some _ -> opt | None -> if x = y then Some ty else None) e None

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module ITbl =
  
  /// Given an interface table t, returns t with the definition
  /// _VarInt = { _val:int } added, which is needed for the 
  /// canonisation of while terms.
  let initialise (t: ITbl) : ITbl =
    let varIntDefn = 
      let defs = Map.ofList [("_val", IFld Int)]
      Eqn defs
    Map.add "_VarInt" varIntDefn t

  /// Given an interface table t and interface identifier i, returns 
  /// all the methods m:(ty_1,..,ty_n) -> ty specified by i in t, 
  /// as a list of triples (m, [ty_1,..,ty_n], ty).
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

  /// Given an interface table t and interface identifier i, returns
  /// all the fields f:ty specified by i in t, as a list of pairs
  /// of the form (f, ty)
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

  /// Given an interface table d, returns true if d is well-formed
  /// according to the rules banning recursive declarations of interfaces.
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

    

module Type =

  /// Given the type of an interface (Iface i), returns the interface i.
  let toInterface (ty: Ty) : IntId =
    match ty with
    | Iface i -> i
    | _ -> failwith "Expected an interface type."


  /// Given an interface table d, an interface identifier i and the name f 
  /// of a field f: ty, if f is in i then returns Some ty and otherwise None.
  let rec tryOfFld (d: ITbl) (i: IntId) (f: FldId) : Option<Ty> =
    let foo (m: IDfnMap) : Option<Ty> =
      match Map.tryFind f m with
      | None -> None
      | Some (IFld ty) -> Some ty
      | Some (IMth _)  -> failwith "Expected field."
    match d.[i] with
    | Eqn m -> foo m
    | Ext (j, m) ->
        match foo m with
        | None -> tryOfFld d j f
        | Some ty -> Some ty

  /// Given an interface table d, an interface identifier i and the name f 
  /// of a field f: ty belonging to that interface, returns the type ty of 
  /// the field.
  let ofFld (d:ITbl) (i:IntId) (f:FldId) : Ty =
    Option.get (tryOfFld d i f)

  /// Given an interface table d, an interface identifier i and the name mth 
  /// of a method mth:(ty_1,...,ty_n) -> ty, if mth belongs to interface i then
  /// returns the type of the method as a pair ([ty_1;..;ty_n],ty) and returns None otherwise.
  let rec tryOfMeth (d: ITbl) (i: IntId) (mth: MethId) : Option<List<Ty> * Ty> =
    let foo (m: IDfnMap) : Option< (List<Ty>*Ty) > =
      match Map.tryFind mth m with
      | None -> None
      | Some (IFld _) -> failwith "Expected method."
      | Some (IMth (ins,out))  -> Some (ins,out)
    match d.[i] with
    | Eqn m -> foo m
    | Ext (j, m) ->
        match foo m with
        | None -> tryOfMeth d j mth
        | Some x -> Some x

  /// Given an interface table d, an interface identifier i and the name mth 
  /// of a method mth:(ty_1,...,ty_n) -> ty belonging to that interface, 
  /// returns the type of the method as a pair ([ty_1;..;ty_n],ty).
  let rec ofMeth (d: ITbl) (i: IntId) (mth: MethId) : (List<Ty> * Ty) =
    Option.get (tryOfMeth d i mth)


  /// Given an interface table d and a type t, returns true if t is
  /// ground (from the G fragment) and false otherwise.
  let rec isG (d: ITbl) (t: Ty) : Bool =
    match t with
    | Int | Void -> true
    | Iface i ->
        let flds = ITbl.fields d i
        let mths = ITbl.methods d i
        List.isEmpty mths && List.forall (isG d << snd) flds

  /// Given an interface table d and a type t, returns true if t is
  /// from the L fragment and false otherwise.
  let rec isL (d: ITbl) (t: Ty) : Bool =
    match t with
    | Int | Void -> true
    | Iface i -> 
        let flds = ITbl.fields d i
        let mths = ITbl.methods d i
        let fldsAreG = List.forall (isG d << snd) flds
        let isGtoL (_,tys,ty) =
          List.forall (isG d) tys && isL d ty 
        let mthsAreGtoL = List.forall isGtoL mths
        fldsAreG && mthsAreGtoL

  /// Given an interface table d and a type t, returns true if t is
  /// from the R fragment and false otherwise.
  let rec isR (d: ITbl) (t: Ty) : Bool =
    match t with
    | Int | Void -> true
    | Iface i ->
        let flds = ITbl.fields d i
        let mths = ITbl.methods d i
        let fldsAreG = List.forall (isG d << snd) flds
        let isLtoG (_,tys,ty) =
          List.forall (isL d) tys && isG d ty 
        let mthsAreLtoG = List.forall isLtoG mths
        fldsAreG && mthsAreLtoG

  /// Given an interface table d and a type t, returns true if t is
  /// from the B fragment and false otherwise.
  let rec isB (d: ITbl) (t: Ty) : Bool =
    isL d t && isR d t

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

