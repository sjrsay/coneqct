namespace IMJEquiv
open IMJEquiv

type State =
  inherit System.IComparable

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

type IntState =
  {
    Val : Int
  }

  interface State with
    member x.CompareTo (yobj: Object) : Int =
      match yobj with
      | :? IntState as y -> compare x y  
      | _ -> 1

type PairState =
  {
    State : State
    Store : SymStore
  }
  
  interface State with
    member x.CompareTo (yobj: Object) : Int =
      match yobj with
      | :? PairState as y -> compare x y  
      | _ -> -1

type Label = Move * SymStore

// This needs looked at
type StackConst = State

type TransLabel =
  | Push of Set<RegId> * Label * StackConst * Set<RegId>
  | Pop of  Set<RegId> * Label * StackConst * Set<RegId> * Set<RegId>
  | Noop of Set<RegId> * Label

type Transition =
  | SetT of State * Set<RegId> * State
  | LabelT of State * TransLabel * State
  | PermT of State * Map<RegId, RegId> * State

type Player =
  | O
  | P

type Automaton =
 {
   States : List<State>
   Owner : Map<State,Player>
   InitS : State
   TransRel : List<Transition>
   InitR : List<RegId>
   Final : List<State>
   Rank : Map<State,SymStore>
 }

module Automata = 

  let maxint = 5

  let updStore (s: SymStore) (k: RegId) (f: FldId) (v: Val) : SymStore =
    let upd (i, m) =
      let newMap = 
        Map.update f (fun _ -> v) m
      (i, newMap)
    Map.update k upd s

  let labelOfTrans (t: Transition) : Option<Label> =
    match t with
    | LabelT (_, tl, _) ->
        match tl with
        | Push (_, l, _, _)
        | Pop  (_, l, _, _, _)
        | Noop (_, l)       -> Some l
    | _                 -> None

  let permuteVal (p: Perm<RegId>) (v: Val) : Val =
    match v with
    | Reg r -> Reg p.[r]
    | _     -> v

  let permuteFields (p: Perm<RegId>) (m: Map<FldId, Val>) : Map<FldId, Val> =
    Map.map (fun _ v -> permuteVal p v) m

  let postApplyPerm (p: Perm<RegId>) (s: SymStore) : SymStore =
    Map.map (fun _ (i, v) ->  (i, permuteFields p v)) s

//  let storesOfAutomaton (a: Automaton) : Set<Store> =
//    let folder (ss: Set<Store>)  


//  let renStore (s: SymStore) (ren: Map<RegId, RegId>) : SymStore =
//    let tryapplyR (r: RegId) : RegId =
//      if Map.containsKey r ren then ren.[r] else r
//    let tryapply (x : Val) : Val =
//      match x with
//      | Num _
//      | Star
//      | Nul -> x
//      | Reg r -> Reg (tryapplyR r)
//    let folder acc r (i, m) =
//      let innerfolder acc f v = Map.add f (tryapply v) acc
//      Map.add (tryapplyR r) (i, Map.fold innerfolder Map.empty m) acc 
//    Map.fold folder Map.empty s
    

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
   
  let storeSuppSplit (s: SymStore) : Set<RegId> * Set<RegId> =
    let getInnerVals acc f v =
      match v with
      | Reg r -> Set.add r acc
      | _     -> acc
    let getOuterVals acc _ (_,m) =
      Map.fold getInnerVals acc m
    let cod = Map.fold getOuterVals Set.empty s
    (Map.domain s, cod)

  let storeSupp (s: SymStore) : Set<RegId> =
    let dom, cod = storeSuppSplit s
    Set.union dom cod

  let labelSupp ((m,s): Label) : Set<RegId> =
    Set.union (moveSupp m) (storeSupp s)

  let trim (s: SymStore) (rs: Set<RegId>) : SymStore =
    let rec fix rs =
      let s' =
        Map.filter (fun r _ -> Set.contains r rs) s
      let newrs = Set.union (storeSupp s') rs
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
        let spp = storeSupp s'
        let s0' = Map.filter (fun k _ -> not (Set.contains k spp)) s0
        for s'' in vals d freeRegs fs s' s0' do
          let z' = storeSupp s''
          if z = z' then acc := s'' :: !acc
          else acc := !acc @ stores d s'' s0' z' // shouldn't this be just acc := stores d s'' s0' z'?
        !acc

  let private stateCount = ref 0

  let newState () : State =
    do stateCount := !stateCount + 1
    { Val = !stateCount } :> State

  let twoStateAuto (l: Label) (s0: SymStore) (sF: SymStore) : Automaton =
    let q0 = newState ()
    let qF = newState ()
    let owner = Map.ofList [(q0, P); (qF, O)]
    let rank = Map.ofList  [(q0, s0); (qF, sF)]
    let trans =
      LabelT (q0, Noop (Set.empty, l), qF)
    {
      States = [q0; qF]
      Owner = owner
      InitS = q0
      TransRel = [trans]
      InitR = Set.toList (labelSupp l)
      Final = [qF]
      Rank = rank
    }


  let nu (d: ITbl) (a: Automaton) (r0: SymStore) : Automaton =
    let q0' = { State = a.InitS; Store = r0 }
    
    let rec fix (ts: Set<Transition>, rs: Set<SymStore>, frontier: Set<SymStore>) : Set<Transition> * Set<SymStore> * Set<SymStore> =
      if Set.isEmpty frontier 
      then 
        (ts, rs, frontier) 
      else
        let folder (ts', rs', fs') (r: SymStore) =
          let mkTransFromTrans (acc: Set<Transition>, newrs: Set<SymStore>) (t: Transition) : Set<Transition> * Set<SymStore> =
            let domR = Map.domain r
            let inQ' q r = (Map.isSubset r a.Rank.[q]) && Set.isEmpty (Set.intersect domR (Map.codomain (Map.difference a.Rank.[q] r)))
            match t with
            | SetT (qo, x, qo') when a.Owner.[qo] = O && (inQ' qo r) ->
                if Set.isSubset domR x
                then
                  let x' = Set.difference x domR
                  let qor = { State = qo; Store = r } :> State 
                  let qo'r = { State = qo'; Store = r } :> State
                  let acc' = Set.add (SetT (qor, x', qo'r)) acc
                  (acc', newrs)
                else 
                  (acc, newrs)
            | SetT (qp, x, qp') when a.Owner.[qp] = P && (inQ' qp r) ->
                let r' = Map.restrict r x
                let x' = Set.difference x (Map.domain r)
                let qpr = { State = qp; Store = r } :> State
                let qp'r' = { State = qp'; Store = r' } :> State
                let acc' = Set.add (SetT (qpr, x', qp'r')) acc
                let newrs' = if Set.contains r' rs then newrs else Set.add r' newrs
                (acc', newrs')
            | PermT (qo, pi, qo') when inQ' qo r ->
                let r' = postApplyPerm pi (Perm.preApply r pi)
                let qor = { State = qo; Store = r } :> State
                let qo'r = { State = qo'; Store = r' } :> State
                let t = PermT (qor, pi, qo'r)
                let acc' = Set.add t acc
                let newrs' = if Set.contains r' rs then newrs else Set.add r' newrs 
                (acc', newrs')
            | LabelT (qo, tl, qp') when a.Owner.[qo] = O && (inQ' qo r) ->
                match tl with
                | Push _ -> failwith "Push transition on an O-state"
                | Pop  (x, (mu, s), _, _, _) 
                | Noop (x, (mu, s))       ->
                    let domR = Map.domain r
                    let sMinusR = Map.difference s r
                    let suppMu = moveSupp mu
                    let b1 = Map.isSubset r s
                    let notInDomR = Set.unionMany [x; suppMu; (Map.codomain sMinusR)]
                    let b2 = Set.isEmpty (Set.intersect domR notInDomR)
                    // let b2 = Set.isEmpty (Set.intersect x domR)
                    // let b3 =
                    //   let cond1 ri = not (Set.contains ri suppMu)
                    //   let cond2 ri = not (Set.contains ri (Map.domain (Map.difference s r)))
                    //   Set.forall (fun ri -> cond1 ri && cond2 ri) domR
                    let acc' =
                      if b1 && b2 then
                        let qor = { State = qo; Store = r } :> State
                        let qp'r = { State = qp'; Store = r } :> State
                        let acc' = 
                          let tl' =
                            match tl with
                            | Push _ -> failwith "Push transition on an O-state"
                              //    let newq = { State = q; Store = r } :> State 
                              //    Push (x, (mu, s), newq, y)
                            | Pop  (_, _, q, y, z) -> 
                                let newq = { State = q; Store = r } :> State
                                let y' = Set.difference y domR
                                let z' = Set.difference z domR
                                Pop  (x, (mu, sMinusR), newq, y', z')
                            | Noop  _ ->
                                Noop (x, (mu, sMinusR))
                          Set.add (LabelT (qor, tl', qp'r)) acc
                        acc'
                      else 
                        acc
                    (acc', newrs)
            | LabelT (qp, tl, qo') when a.Owner.[qp] = P && (inQ' qp r) ->
                match tl with
                | Pop  _ -> failwith "Pop transition on a P-state"
                | Push (x, (mu, s), _, _) 
                | Noop (x, (mu, s))       ->
                    let qpr = { State = qp; Store = r } :> State
                    let suppMu = moveSupp mu
                    let domS = Map.domain s
                    let domR = Map.domain r
                    let zStore = trim s (Set.union suppMu (Set.difference domS (Set.union x domR)))
                    let z = storeSupp zStore
                    let s' = Map.restrict s z
                    let r' = Map.difference s s'
                    let x' = Set.intersect (Set.union x domR) z
                    let qo'r' = { State = qo'; Store = r' } :> State
                    let tl' = 
                      match tl with
                      | Pop _ -> failwith "Pop transition on a P-state"
                        //   let newq = { State = q; Store = r' } :> State
                        //   Pop  (x', (mu, s'), newq, y)
                      | Push (_, _, q, y) ->
                          let newq = { State = q; Store = r' } :> State 
                          let y' = Set.difference y (Map.domain r')
                          Push (x', (mu, s'), newq, y')
                      | Noop  _ -> Noop (x', (mu, s')) 
                    let acc' = Set.add (LabelT (qpr, tl', qo'r')) acc
                    let newrs' = if Set.contains r' rs then newrs else Set.add r' newrs
                    (acc', newrs')
            | _ -> (acc, newrs) // we should only get here if "inQ' q r" is false
          let newTrans, newFront = List.fold mkTransFromTrans (ts', fs') a.TransRel
          let newRs = Set.union rs' newFront
          (newTrans, newRs, newFront) 
        let newts, newrs, newfs = Set.fold folder (ts, rs, Set.empty) frontier 
        fix (newts, newrs, newfs)   
      
    let newts, newrs, _ = fix (Set.empty, Set.singleton r0, Set.singleton r0)
    let stPairs = Set.product (set a.States) newrs
    let owner = Set.fold (fun m (q,r) -> Map.add ({ State = q; Store = r } :> State) (a.Owner.[q]) m) Map.empty stPairs
    let rank =
      let ranker m (q,r) = Map.add ({ State = q; Store = r } :> State) (Map.difference a.Rank.[q] r) m
      Set.fold ranker Map.empty stPairs
    let finals = Set.fold (fun xs (q,r) -> { State = q; Store = r } :> State :: xs) [] stPairs
    {
      States = Map.domainList owner
      Owner = owner
      InitS = q0'
      TransRel = Set.toList newts
      InitR = Set.toList (Set.difference (set a.InitR) (Map.domain r0))
      Final = finals
      Rank = rank
    }
      


  let rec fromCanon (d: ITbl) (g: TyEnv) (cn: Canon) (mu: List<Move>) (s: SymStore) : Automaton =
    match cn with
    | NullR -> twoStateAuto (ValM Nul, s) s s
    | Var x -> 
        let k = Types.getPosInTyEnv x g
        twoStateAuto (mu.[k], s) s s
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
     | Let (x, CanLet.Call (y,m,zs), c) ->
        let (Iface yi) = Types.getTyfromTyEnv y g
        let (_, xty) = Types.ofMeth d yi m
        let (ValM (Reg rj)) = mu.[Types.getPosInTyEnv y g]
        let mapper z : Val =
          match mu.[Types.getPosInTyEnv z g] with
            | ValM v -> v
            | _ -> failwith "Expected a value move."
        let vs = List.map mapper zs
        let q0 = newState ()
        let q1 = newState ()
        let callm = Call (rj, m, vs)
        let l = Noop (Set.empty, (callm, s))
        let calltr = LabelT (q0, l, q1)

        let states0 = [q0; q1]
        let owner0 q = if q=q0 then P else O
        let trel0 = [calltr]
        let final0 = []
        let initS0 = q0
        let initR0 = Set.toList (Map.domain s)
        
        let getPair st =
          let oldrs = Map.domain s
          let newrs = Map.domain st
          let nuX = Set.difference newrs oldrs
          (nuX, newrs)
        match xty with
          | Void ->
              let z0 = muSupp mu
              let allStores = stores d Map.empty s z0
              let folder (states, owner, trel, final) s0' =
                let (nuX, rY) = getPair s0'
                let mu' = List.append mu [ValM Star]
                let g'  = List.append g [(x, xty)]
                let autoc = fromCanon d g' c mu' s0'
                let q' = newState ()
                let ret1 = LabelT (q1, Noop (nuX, (Ret (rj,m,Star), s0')), q')
                let ret2 = SetT (q', rY, autoc.InitS)
                let states' = q' :: states @ autoc.States
                let owner' q =  // owner should really be a Map
                  if q=q' then P
                  else if List.contains q states then (owner q) else (autoc.Owner q)
                let trel' = [ret1; ret2] @ trel @ autoc.TransRel
                let final' = final @ autoc.Final
                (states', owner', trel', final')
              let (states, owner, trel, final) = List.fold folder (states0, owner0, trel0, final0) allStores 
              {
                States = states
                Owner = owner
                InitS = initS0
                TransRel = trel
                InitR = initR0
                Final = final
              }
          | Iface i ->
              let z0 = muSupp mu
              let domS = Map.domain s
              let rj's = (nextReg domS) :: Set.toList domS
              let rj'folder (states', owner', trel', final') rj' =
                let z0' = Set.add rj' z0 
                let allStores = stores d Map.empty s z0'
                let mu' = List.append mu [ValM (Reg rj')]
                let g'  = List.append g [(x, xty)]
                let s0'folder (states, owner, trel, final) s0' =
                  let (nuX, rY) = getPair s0'
                  let autoc = fromCanon d g' c mu' s0'
                  let q' = newState ()
                  let ret1 = LabelT (q1, Noop (nuX, (Ret (rj,m,Reg rj'), s0')), q')
                  let ret2 = SetT (q', rY, autoc.InitS)
                  let states'' = q' :: states @ autoc.States
                  let owner'' q =  // owner should really be a Map
                    if q=q' then P
                    else if List.contains q states then (owner q) else (autoc.Owner q)
                  let trel'' = [ret1; ret2] @ trel @ autoc.TransRel
                  let final'' = final @ autoc.Final
                  (states'', owner'', trel'', final'')
                let (states, owner, trel, final) = List.fold s0'folder (states', owner', trel', final') allStores 
                (states, owner, trel, final)
              let (states, owner, trel, final) = List.fold rj'folder (states0, owner0, trel0, final0) rj's
              {
                States = states
                Owner = owner
                InitS = initS0
                TransRel = trel
                InitR = initR0
                Final = final
              }  
          | Int ->
              let z0 = muSupp mu
              let domS = Map.domain s
              let allStores = stores d Map.empty s z0
              let s0'folder (states, owner, trel, final) s0' =
                let (nuX, rY) = getPair s0'
                let jfolder (states', owner', trel', final') j =
                  let mu' = List.append mu [ValM (Num j)]
                  let g'  = List.append g [(x, xty)]
                  let autoc = fromCanon d g' c mu' s0'
                  let q' = newState ()
                  let ret1 = LabelT (q1, Noop (nuX, (Ret (rj,m,Num j), s0')), q')
                  let ret2 = SetT (q', rY, autoc.InitS)
                  let states'' = q' :: states @ autoc.States
                  let owner'' q =  // owner should really be a Map
                    if q=q' then P
                    else if List.contains q states then (owner q) else (autoc.Owner q)
                  let trel'' = [ret1; ret2] @ trel @ autoc.TransRel
                  let final'' = final @ autoc.Final
                  (states'', owner'', trel'', final'')
                let js = [0..maxint]
                let (states', owner', trel', final') = List.fold jfolder (states, owner, trel, final) js
                (states', owner', trel', final')
              let (states, owner, trel, final) = List.fold s0'folder (states0, owner0, trel0, final0) allStores
              {
                States = states
                Owner = owner
                InitS = initS0
                TransRel = trel
                InitR = initR0
                Final = final
              }
     | Let (_, While (r, c1), c2) -> 
         let (ValM (Reg rk')) = mu.[Types.getPosInTyEnv r g]
         if (snd s.[rk']).["val"] = Num 0 then
           fromCanon d g c2 mu s
         else
           

//  and fromCanLet (d: TyEnv) (g: ITbl) (c: CanLet) (l: Label) : Automaton =
//    match c with
//    | Skip -> 
