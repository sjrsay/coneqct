namespace IMJEquiv

/// The type of values
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

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Val =

  /// The maximum integer.
  /// This will be the maximum of 1, the largest constant
  /// occurring in either of the terms and the value of
  /// the -maxint option (where specified).
  let mutable maxint = 1

  /// Given integers i and j, returns the minimum of (i+j) and maxint.
  let add (i:Int) (j:Int) : Int =
    min (i+j) maxint

  /// Given integers i and j, returns the maxinum of (i-j) and 0.
  let sub (i:Int) (j:Int) : Int =
    max (i-j) 0

  /// Given a value v, returns the support of v.
  let supp (v: Val) : Set<RegId> =
    match v with
    | VNum _ 
    | VStar 
    | VNul    -> Set.empty
    | VReg r  -> Set.singleton r 

  /// Given a permutation p on register ids and a value v,
  /// such that supp v <= dom r;
  /// returns v with each occurrence of a register id r
  /// replaced by p.[r].  
  let permute (p: Perm<RegId>) (v: Val) : Val =
    match v with
    | VReg r -> VReg p.[r]
    | _      -> v

  /// Given a type ty, returns the default
  /// value inhabiting that type.
  let defaultOfTy (ty: Ty) : Val =
    match ty with
    | Void    -> VStar
    | Int     -> VNum 0
    | Iface _ -> VNul
