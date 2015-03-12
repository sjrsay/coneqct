namespace IMJEquiv

/// The type of single moves.  
/// Note we represent tupled moves rather as List<Move>.
type Move = 
  | ValM of Val
  | Call of RegId * MethId * List<Val>
  | Ret of RegId * MethId * Val

  override x.ToString () =
    match x with
    | ValM v -> v.ToString ()
    | Call (r, mth, vs) -> sprintf "call %d.%s(%s)" r mth (List.toStringWithDelims "" "," "" vs)
    | Ret (r, mth, v) -> sprintf "ret %d.%s(%O)" r mth v

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Move =

  /// Given a move m, returns the support of m.
  let rec supp (m: Move) : Set<RegId> =
    match m with
    | ValM v -> Val.supp v
    | Call (r,mth,vs) -> 
        List.fold (fun rvs v -> Set.union (Val.supp v) rvs) (Set.singleton r) vs
    | Ret (r,mth,v) ->
        Set.add r (Val.supp v)


  /// Given an integer move (ValM (VNum i)), returns i.
  let toInt (m: Move) : Int =
    match m with 
    | ValM (VNum i) -> i
    | _ -> failwith "Expected an integer move."

  /// Given a register move (ValM (VReg r)), returns r.
  let toRegister (m: Move) : RegId =
    match m with
    | ValM (VReg r) -> r
    | _ -> failwith "Expected a register move."

  /// Given a move list ms, returns its string representation.
  let listToString (ms: List<Move>) : String =
    match ms with
    | []   -> ""
    | [x]  -> x.ToString ()
    | _::_ -> List.toStringWithDelims "(" ", " ")" ms

  /// Given register index rnum and type environment g, 
  /// with g = [x_1:t_1; ...; x_n:t_n], ofContext rnum g is
  /// [m_1; ...; m_2] with `_i a possible initial move
  /// corresponing to the x_i:t_i.  If t_i is an interface
  /// then m_i is determined as the move ValM (VReg r)
  /// where r is the smallest register number not occurring
  /// in [m_1, ..., m_{i-1}] that is no smaller than rnum.
  let ofContext (rnum: Int) (g: TyEnv) : List<List<Move>> =

    let allOfTy (r: Int) (ty: Ty) : Int * List<Val> =
      match ty with
      | Void -> (r, [VStar])
      | Int  -> (r, [for i in 0 .. Val.maxint do yield VNum i])
      | Iface i -> (r+1, [VReg r])
    
    let rec mkMoves r gs =
      match gs with
      | [] -> [[]]
      | (x,ty)::gs' ->
          let r', vs = allOfTy r ty
          [for v in vs do for ms in mkMoves r' gs' do yield ValM v :: ms]
    
    mkMoves rnum g
