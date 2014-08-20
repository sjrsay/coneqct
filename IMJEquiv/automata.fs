namespace IMJEquiv
open IMJEquiv

type State = Int32

type RegId = Int32

type Val =
  | Num of Int32
  | Star
  | Nul
  | Reg of RegId

type Move = 
  | ValM of Val
  | Call of RegId * MethId * List<Val>
  | Ret of RegId * MethId * Val

type SymStore =
  Map<RegId, IntId * Map<FldId, Val>>

type Label = Move * SymStore

// This needs looked at
type StackConst = State

type TransLabel =
  | Push of Set<RegId> * Label * StackConst * Set<RegId>
  | Pop of  Set<RegId> * Label * StackConst * Set<RegId>
  | Noop of Set<RegId> * Label

type Transition =
  | SetT of State * Set<RegId> * State
  | LabelT of State * TransLabel * State

type Player =
  | O
  | P

type Automaton =
 {
   States : List<State>
   Owner : State -> Player
   InitS : State
   TransRel : List<Transition>
   InitR : List<RegId>
   Final : List<State>
 }

module Automata = 

  let maxint = 5

  let updStore (s: SymStore) (k: RegId) (f: FldId) (v: Val) : SymStore =
    let upd (i, m) =
      let newMap = 
        Map.update f (fun _ -> v) m
      (i, newMap)
    Map.update k upd s

  let valSupp (v: Val) : Set<RegId> =
    match v with
    | Num _ 
    | Star 
    | Nul    -> Set.empty
    | Reg r  -> Set.singleton r 
  
  let rec moveSupp (m: Move) : Set<RegId> =
    match m with
    | ValM v -> valSupp v
    | Call (r,mth,vs) -> 
        List.fold (fun rvs v -> Set.union (valSupp v) rvs) (Set.singleton r) vs
    | Ret (r,mth,v) ->
        Set.add r (valSupp v)

  let muSupp (ms: List<Move>) : Set<RegId> =
    List.fold (fun acc m -> Set.union acc (moveSupp m)) Set.empty ms

  let storeTypedSupp (d: ITbl) (s: SymStore) : Set<RegId * IntId> =
    let getInnerVals i acc f v =
      match v with
      | Reg r -> 
          let (Iface j) = Types.ofFld d i f
          Set.add (r, j) acc
      | _     -> acc
    let getOuterVals acc r (i,m) =
      Map.fold (getInnerVals i) (Set.add (r, i) acc) m
    Map.fold getOuterVals Set.empty s
   
  let storeSupp (d: ITbl) (s: SymStore) : Set<RegId> =
    Set.map fst (storeTypedSupp d s)

  let labelSupp (d: ITbl) ((m,s): Label) : Set<RegId> =
    Set.union (moveSupp m) (storeSupp d s)

  let trim (d: ITbl) (s: SymStore) (rs: Set<RegId>) : SymStore =
    let rec fix rs =
      let s' =
        Map.filter (fun r _ -> Set.contains r rs) s
      let newrs = Set.union (storeSupp d s') rs
      if newrs = rs then rs else fix newrs
    let supp = fix rs
    Map.filter (fun r _ -> Set.contains r supp) s

  let fields (s: SymStore) (r: RegId) : IntId * List<FldId> =
    let i, m = s.[r]
    (i, Map.domainList m)

  let nextReg (rs: Set<RegId>) : RegId =
    let n = ref 1
    while Set.contains !n rs do
      n := !n + 1
    !n

  let rec vals (d: ITbl) (rs: List<RegId>) (fs: List<FldId>) (s: SymStore) (s0': SymStore) : List<SymStore> =
    match rs with
    | [] -> [s]
    | r::rs' ->
        match fs with
        | [] -> 
            match rs' with
            | [] -> [s]
            | r'::rs'' ->
                let i, fs = fields s r'
                let s' = Map.add r' (i, Map.empty) s
                vals d rs' fs s' s0'
        | f::fs' ->
            let acc = ref []
            let rIface = fst s.[r]
            match Types.ofFld d rIface f with
            | Ty.Int ->
                for x in [0..maxint] do
                  let s' = Map.update r (fun (i, m) -> (i, Map.add f (Num x) m)) s
                  let ss = vals d rs fs' s' s0'
                  acc := List.append ss !acc
                !acc   
            | Ty.Void ->
                let s' = Map.update r (fun (i, m) -> (i, Map.add f Star m)) s
                vals d rs fs' s' s0'
            | Ty.Iface i ->
                let sTypedSupp = storeTypedSupp d s
                let s0'TypedSupp = storeTypedSupp d s0'
                let sFilteredSupp = Set.fold (fun acc (r, j) -> if i = j then r :: acc else acc) [] sTypedSupp
                let s0'FilteredSupp = Set.fold (fun acc (r, j) -> if i = j && Set.contains r (Map.domain s0') then r :: acc else acc) [] s0'TypedSupp
                let fresh = nextReg (Set.union (Set.map fst sTypedSupp) (Map.domain s0'))
                let choices = fresh :: sFilteredSupp @ s0'FilteredSupp
                for x in choices do
                  let s' = Map.update r (fun (i, m) -> (i, Map.add f (Reg x) m)) s
                  let s0'' = Map.remove x s0'
                  let ss = vals d rs fs' s' s0''
                  acc := List.append ss !acc
                !acc

  let rec stores (d: ITbl) (s: SymStore) (s0: SymStore) (z: Set<RegId>) : List<SymStore> =
    let freeRegs = Set.toList (Set.difference z (Map.domain s))
    let acc = ref []
    match freeRegs with
    | []    -> [s]
    | r::rs ->
        let i, fs = fields s r
        let s' = Map.add r (i, Map.empty) s
        let spp = storeSupp d s'
        let s0' = Map.filter (fun k _ -> not (Set.contains k spp)) s0
        for s'' in vals d freeRegs fs s' s0' do
          let z' = storeSupp d s''
          if z = z' then acc := s'' :: !acc else acc := !acc @ stores d s'' s0' z'
        !acc

  let private stateCount = ref 0

  let newState () : State =
    do stateCount := !stateCount + 1
    !stateCount

  let twoStateAuto (l: Label) : Automaton =
    let q0 = newState ()
    let qF = newState ()
    let owner q =
      if q = q0 then P else O
    let trans =
      LabelT (q0, Noop (Set.empty, l), qF)
    {
      States = [q0; qF]
      Owner = owner
      InitS = q0
      TransRel = [trans]
      InitR = Set.toList (labelSupp l)
      Final = [qF]
    }

  let rec fromCanon (d: ITbl) (g: TyEnv) (cn: Canon) (mu: List<Move>) (s: SymStore) : Automaton =
    match cn with
    | NullR -> twoStateAuto (ValM Nul, s)
    | Var x -> 
        let k = Types.getPosInTyEnv x g
        twoStateAuto (mu.[k], s)
    | If (x, c1, c0) ->
        let k = Types.getPosInTyEnv x g
        if mu.[k] = ValM (Num 0) then
          fromCanon d g c0 mu s 
        else
          fromCanon d g c1 mu s
    | Let (_, Assn (x,f,y), c) ->
        let (ValM (Reg rk')) = mu.[Types.getPosInTyEnv x g]
        let (ValM (Reg rj')) = mu.[Types.getPosInTyEnv y g]
        let newStore = updStore s rk' f (Reg rj')
        let trimmedStore = trim newStore (muSupp mu)
        let cAuto = fromCanon d g c mu trimmedStore
        let q0 = newState ()
        let owner q =
          if q = q0 then P else cAuto.Owner q 
        let trans = 
          SetT (q0, Map.domain trimmedStore, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = Map.domainList s
          Final = cAuto.Final
        }
     | Let (x, NullL ty, c) ->
        let q0 = newState ()
        let mu' = List.append mu  [ValM Nul]
        let g' = List.append g [(x, ty)]
        let cAuto = fromCanon d g' c mu' s
        let owner q =
          if q = q0 then P else cAuto.Owner q 
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
        }
     | Let (x, CanLet.Num i, c) ->
        let q0 = newState ()
        let mu' = List.append mu  [ValM (Num i)]
        let g' = List.append g [(x, Int)]
        let cAuto = fromCanon d g' c mu' s
        let owner q =
          if q = q0 then P else cAuto.Owner q 
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
        }
     | Let (x, Skip, c) ->
        let q0 = newState ()
        let mu' = List.append mu  [ValM Star]
        let g' = List.append g [(x, Void)]
        let cAuto = fromCanon d g' c mu' s
        let owner q =
          if q = q0 then P else cAuto.Owner q 
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
        } 
     | Let (x, Plus (y,z), c) ->
        let q0 = newState ()
        let (ValM (Num yval)) = mu.[Types.getPosInTyEnv y g]
        let (ValM (Num zval)) = mu.[Types.getPosInTyEnv z g]
        let mu' = List.append mu  [ValM (Num (yval + zval))]
        let g' = List.append g [(x, Int)]
        let cAuto = fromCanon d g' c mu' s
        let owner q =
          if q = q0 then P else cAuto.Owner q 
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
        }
     | Let (y, Eq (x1, x2), c) -> 
        let q0 = newState ()
        let (ValM (Reg x1val)) = mu.[Types.getPosInTyEnv x1 g]
        let (ValM (Reg x2val)) = mu.[Types.getPosInTyEnv x2 g]
        let cmp = if x1val = x2val then 1 else 0
        let mu' = List.append mu  [ValM (Num cmp)]
        let g' = List.append g [(y, Int)]
        let cAuto = fromCanon d g' c mu' s
        let owner q =
          if q = q0 then P else cAuto.Owner q 
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
        }
     | Let (y, Cast (i, x), c) ->
         let (ValM (Reg rk')) = mu.[Types.getPosInTyEnv x g]
         let j, _ = s.[rk']
         if Types.subtype d j i then 
           let mu' = List.append mu [ValM (Reg rk')]
           fromCanon d g c mu' s
         else
           let q0 = newState ()
           {
             States = [q0]
             Owner = fun _ -> P
             InitS = q0
             TransRel = []
             InitR = Map.domainList s
             Final = []
           }
     | Let (y, Fld (x,f), c) -> 
        let q0 = newState ()
        let (ValM (Reg rk')) = mu.[Types.getPosInTyEnv x g]
        let (i,m) = s.[rk']
        let v  = m.[f]
        let ty = Types.ofFld d i f 
        let mu' = List.append mu  [ValM v]
        let g' = List.append g [(y, ty)]
        let cAuto = fromCanon d g' c mu' s
        let owner q =
          if q = q0 then P else cAuto.Owner q 
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
        }

//  and fromCanLet (d: TyEnv) (g: ITbl) (c: CanLet) (l: Label) : Automaton =
//    match c with
//    | Skip -> 