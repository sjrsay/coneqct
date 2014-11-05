namespace IMJEquiv
open IMJEquiv
open System

type State =
  inherit IComparable

[<CustomComparison>]
[<StructuralEquality>]
type IntState =
  {
    Val : Int
  }

  interface State with
    override x.CompareTo (yobj: Object) : Int =
      match yobj with
      | :? IntState as y -> compare x y  
      | _ -> 1

[<CustomComparison>]
[<StructuralEquality>]
type PairState =
  {
    State : State
    Store : Store
  }
  
  interface State with
    member x.CompareTo (yobj: Object) : Int =
      match yobj with
      | :? PairState as y -> compare x y  
      | _ -> -1

type Label = Move * Store

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
   Rank : Map<State,Store>
 }

module Automata = 

  let maxint = 5

  let labelOfTrans (t: Transition) : Option<Label> =
    match t with
    | LabelT (_, tl, _) ->
        match tl with
        | Push (_, l, _, _)
        | Pop  (_, l, _, _, _)
        | Noop (_, l)       -> Some l
    | _                 -> None

//  let storesOfAutomaton (a: Automaton) : Set<Store> =
//    let folder (ss: Set<Store>)  


//  let renStore (s: Store) (ren: Map<RegId, RegId>) : Store =
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
    
 

  let muSupp (ms: List<Move>) : Set<RegId> =
    List.fold (fun acc m -> Set.union acc (Move.supp m)) Set.empty ms

  let labelSupp ((m,s): Label) : Set<RegId> =
    Set.union (Move.supp m) (Store.supp s)

  let private stateCount = ref 0

  let newState () : State =
    do stateCount := !stateCount + 1
    { Val = !stateCount } :> State

  let twoStateAuto (l: Label) (s0: Store) (sF: Store) : Automaton =
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


  let nu (d: ITbl) (a: Automaton) (r0: Store) : Automaton =
    let q0' = { State = a.InitS; Store = r0 }
    
    let rec fix (ts: Set<Transition>, rs: Set<Store>, frontier: Set<Store>) : Set<Transition> * Set<Store> * Set<Store> =
      if Set.isEmpty frontier 
      then 
        (ts, rs, frontier) 
      else
        let folder (ts', rs', fs') (r: Store) =
          let mkTransFromTrans (acc: Set<Transition>, newrs: Set<Store>) (t: Transition) : Set<Transition> * Set<Store> = 
            let domR = Map.domain r
            let inQ' q r = 
              let _, cod = Store.splitSupp (Map.difference a.Rank.[q] r)
              (Map.isSubset r a.Rank.[q]) && Set.isEmpty (Set.intersect domR cod)
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
                let r' = Store.postPermute pi (Perm.preApply r pi)
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
                    let suppMu = Move.supp mu
                    let b1 = Map.isSubset r s
                    let notInDomR = Set.unionMany [x; suppMu; (snd (Store.splitSupp sMinusR))]
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
                    let suppMu = Move.supp mu
                    let domS = Map.domain s
                    let domR = Map.domain r
                    let zStore = Store.trim s (Set.union suppMu (Set.difference domS (Set.union x domR)))
                    let z = Store.supp zStore
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
      
  let isFinalTrans (a: Automaton) (t: Transition) : Bool =
    match t with
    | SetT   (_,_,q)
    | LabelT (_,_,q)
    | PermT  (_,_,q) -> List.contains q a.Final
  
  let getSecondState (t: Transition) : State =
    match t with
    | SetT (_,_,q)
    | PermT (_,_,q)
    | LabelT (_,_,q) -> q

  let rec fromCanon (d: ITbl) (g: TyEnv) (cn: Canon) (mu: List<Move>) (s: Store) : Automaton =
    let x0 = Map.domain s
    match cn with
    | NullR -> twoStateAuto (ValM VNul, s) s s
    | Var x -> 
        let k = Types.getPosInTyEnv x g
        twoStateAuto (mu.[k], s) s s
    | If (x, c1, c0) ->
        let k = Types.getPosInTyEnv x g
        if mu.[k] = ValM (VNum 0) then
          fromCanon d g c0 mu s 
        else
          fromCanon d g c1 mu s
    | Let (_, Assn (x,f,y), c) ->
        let (ValM (VReg rk')) = mu.[Types.getPosInTyEnv x g]
        let (ValM (VReg rj')) = mu.[Types.getPosInTyEnv y g]
        let newStore = Store.update s rk' f (VReg rj')
        let trimmedStore = Store.trim newStore (muSupp mu)
        let cAuto = fromCanon d g c mu trimmedStore
        let q0 = newState ()
        let owner = Map.add q0 P cAuto.Owner 
        let rank = Map.add q0 s cAuto.Rank
        let trans = 
          SetT (q0, Map.domain trimmedStore, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = Map.domainList s
          Final = cAuto.Final
          Rank = rank
        }
     | Let (x, NullL ty, c) ->
        let q0 = newState ()
        let mu' = List.append mu  [ValM VNul]
        let g' = List.append g [(x, ty)]
        let cAuto = fromCanon d g' c mu' s
        let owner = Map.add q0 P cAuto.Owner 
        let rank = Map.add q0 s cAuto.Rank
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
          Rank = rank
        }
     | Let (x, CanLet.Num i, c) ->
        let q0 = newState ()
        let mu' = List.append mu  [ValM (VNum i)]
        let g' = List.append g [(x, Int)]
        let cAuto = fromCanon d g' c mu' s
        let owner = Map.add q0 P cAuto.Owner 
        let rank = Map.add q0 s cAuto.Rank
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
          Rank = rank
        }
     | Let (x, Skip, c) ->
        let q0 = newState ()
        let mu' = List.append mu  [ValM VStar]
        let g' = List.append g [(x, Ty.Void)]
        let cAuto = fromCanon d g' c mu' s
        let owner = Map.add q0 P cAuto.Owner 
        let rank = Map.add q0 s cAuto.Rank
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
          Rank = rank
        } 
     | Let (x, Plus (y,z), c) ->
        let q0 = newState ()
        let (ValM (VNum yval)) = mu.[Types.getPosInTyEnv y g]
        let (ValM (VNum zval)) = mu.[Types.getPosInTyEnv z g]
        let mu' = List.append mu  [ValM (VNum (yval + zval))]
        let g' = List.append g [(x, Int)]
        let cAuto = fromCanon d g' c mu' s
        let owner = Map.add q0 P cAuto.Owner 
        let rank = Map.add q0 s cAuto.Rank
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
          Rank = rank
        }
     | Let (y, Eq (x1, x2), c) -> 
        let q0 = newState ()
        let (ValM (VReg x1val)) = mu.[Types.getPosInTyEnv x1 g]
        let (ValM (VReg x2val)) = mu.[Types.getPosInTyEnv x2 g]
        let cmp = if x1val = x2val then 1 else 0
        let mu' = List.append mu  [ValM (VNum cmp)]
        let g' = List.append g [(y, Int)]
        let cAuto = fromCanon d g' c mu' s
        let owner = Map.add q0 P cAuto.Owner 
        let rank = Map.add q0 s cAuto.Rank
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
          Rank = rank
        }
     | Let (y, Cast (i, x), c) ->
         let (ValM (VReg rk')) = mu.[Types.getPosInTyEnv x g]
         let j, _ = s.[rk']
         if Types.subtype d j i then 
           let mu' = List.append mu [ValM (VReg rk')]
           fromCanon d g c mu' s
         else
           let q0 = newState ()
           let owner = Map.singleton q0 P 
           let rank = Map.singleton q0 s
           {
             States = [q0]
             Owner = owner
             InitS = q0
             TransRel = []
             InitR = Map.domainList s
             Final = []
             Rank = rank
           }
     | Let (y, Fld (x,f), c) -> 
        let q0 = newState ()
        let (ValM (VReg rk')) = mu.[Types.getPosInTyEnv x g]
        let (i,m) = s.[rk']
        let v  = m.[f]
        let ty = Types.ofFld d i f 
        let mu' = List.append mu  [ValM v]
        let g' = List.append g [(y, ty)]
        let cAuto = fromCanon d g' c mu' s
        let owner = Map.add q0 P cAuto.Owner 
        let rank = Map.add q0 s cAuto.Rank
        let trans = 
          SetT (q0, set cAuto.InitR, cAuto.InitS)
        {
          States = q0 :: cAuto.States
          Owner = owner
          InitS = q0
          TransRel = trans :: cAuto.TransRel
          InitR = cAuto.InitR
          Final = cAuto.Final
          Rank = rank
        }
     | Let (x, CanLet.Call (y,m,zs), c) ->
        let (Iface yi) = Types.getTyfromTyEnv y g
        let (_, xty) = Types.ofMeth d yi m
        let (ValM (VReg rj)) = mu.[Types.getPosInTyEnv y g]
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
        let owner0 = Map.ofList [(q0, P); (q1, O)]
        let rank0 = Map.ofList [(q0, s); (q1, s)]
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
              let tyZ0 = Set.map (fun r -> (r, Store.tyOfReg s r)) z0
              let allStores = Store.stores d s tyZ0
              let folder (states, owner: Map<State,Player>, rank, trel, final) s0' =
                let (nuX, rY) = getPair s0'
                let mu' = List.append mu [ValM VStar]
                let g'  = List.append g [(x, xty)]
                let autoc = fromCanon d g' c mu' s0'
                let q' = newState ()
                let ret1 = LabelT (q1, Noop (nuX, (Ret (rj,m,VStar), s0')), q')
                let ret2 = SetT (q', rY, autoc.InitS)
                let states' = q' :: states @ autoc.States
                let owner' = Map.union (Map.add q' P owner) autoc.Owner 
                let rank' = Map.union (Map.add q' s0' rank) autoc.Rank
                let trel' = [ret1; ret2] @ trel @ autoc.TransRel
                let final' = final @ autoc.Final
                (states', owner', rank', trel', final')
              let (states, owner, rank, trel, final) = List.fold folder (states0, owner0, rank0, trel0, final0) allStores 
              {
                States = states
                Owner = owner
                InitS = initS0
                TransRel = trel
                InitR = initR0
                Final = final
                Rank = rank
              }
          | Iface i ->
              let z0 = muSupp mu
              let domS = Map.domain s
              let rj's = (Store.nextReg domS) :: Set.toList domS
              let rj'folder (states', owner', rank', trel', final') rj' =
                let z0' = Set.add rj' z0 
                let tyZ0' = Set.map (fun r -> (r, Store.tyOfReg s r)) z0'
                let allStores = Store.stores d s tyZ0'
                let mu' = List.append mu [ValM (VReg rj')]
                let g'  = List.append g [(x, xty)]
                let s0'folder (states, owner, rank, trel, final) s0' =
                  let (nuX, rY) = getPair s0'
                  let autoc = fromCanon d g' c mu' s0'
                  let q' = newState ()
                  let ret1 = LabelT (q1, Noop (nuX, (Ret (rj,m,VReg rj'), s0')), q')
                  let ret2 = SetT (q', rY, autoc.InitS)
                  let states'' = q' :: states @ autoc.States
                  let owner'' = Map.union (Map.add q' P owner) autoc.Owner
                  let rank'' = Map.union (Map.add q' s0' rank) autoc.Rank
                  let trel'' = [ret1; ret2] @ trel @ autoc.TransRel
                  let final'' = final @ autoc.Final
                  (states'', owner'', rank'', trel'', final'')
                let (states, owner, rank, trel, final) = List.fold s0'folder (states', owner', rank', trel', final') allStores 
                (states, owner, rank, trel, final)
              let (states, owner, rank, trel, final) = List.fold rj'folder (states0, owner0, rank0, trel0, final0) rj's
              {
                States = states
                Owner = owner
                InitS = initS0
                TransRel = trel
                InitR = initR0
                Final = final
                Rank = rank
              }  
          | Int ->
              let z0 = muSupp mu
              let domS = Map.domain s
              let tyZ0 = Set.map (fun r -> (r, Store.tyOfReg s r)) z0
              let allStores = Store.stores d s tyZ0
              let s0'folder (states, owner, rank, trel, final) s0' =
                let (nuX, rY) = getPair s0'
                let jfolder (states', owner', rank', trel', final') j =
                  let mu' = List.append mu [ValM (VNum j)]
                  let g'  = List.append g [(x, xty)]
                  let autoc = fromCanon d g' c mu' s0'
                  let q' = newState ()
                  let ret1 = LabelT (q1, Noop (nuX, (Ret (rj,m,VNum j), s0')), q')
                  let ret2 = SetT (q', rY, autoc.InitS)
                  let states'' = q' :: states @ autoc.States
                  let owner'' = Map.union (Map.add q' P owner') autoc.Owner 
                  let rank'' = Map.union (Map.add q' s0' rank') autoc.Rank
                  let trel'' = [ret1; ret2] @ trel @ autoc.TransRel
                  let final'' = final @ autoc.Final
                  (states'', owner'', rank'', trel'', final'')
                let js = [0..maxint]
                let (states', owner', rank', trel', final') = List.fold jfolder (states, owner, rank, trel, final) js
                (states', owner', rank', trel', final')
              let (states, owner, rank, trel, final) = List.fold s0'folder (states0, owner0, rank0, trel0, final0) allStores
              {
                States = states
                Owner = owner
                InitS = initS0
                TransRel = trel
                InitR = initR0
                Final = final
                Rank = rank
              }
     | Let (_, While (r, c1), c2) -> 
         let (ValM (VReg rk')) = mu.[Types.getPosInTyEnv r g]
         if (snd s.[rk']).["val"] = VNum 0 then
           fromCanon d g c2 mu s
         else
           let z0 = muSupp mu
           let tyZ0 = Set.map (fun r -> (r, Store.tyOfReg s r)) z0
           let allStores = Store.stores d s tyZ0
           let mkNuC c s1 =
             let c'  = fromCanon d g c mu s1
             nu d c' Map.empty 
           let c1s = List.fold (fun c1s str -> Map.add str (mkNuC c1 str) c1s) Map.empty allStores
           let c2s = List.fold (fun c2s str -> Map.add str (mkNuC c2 str) c2s) Map.empty allStores
           let mkTuple (qs, nfts, fts) (a: Automaton) =
             let nfts', fts' = List.partition (isFinalTrans a) a.TransRel
             (qs @ a.States, nfts @ nfts', fts @ fts')
           let c1sStates, c1sTrans, c1sFinals = Set.fold mkTuple ([],[],[]) (Map.codomain c1s)
           let c2sStates, c2sTrans, c2sFinals = Set.fold mkTuple ([],[],[]) (Map.codomain c2s)
           let newC1sTrans = ref c1sTrans
           for t in c1sFinals do
              match t with
              | SetT _ 
              | PermT _ -> failwith "Expected labelled transition as final"
              | LabelT (p, l, p') ->
                match p with
                | :? PairState as ps ->
                    match p' with
                    | :? PairState as ps' -> 
                        let r  = ps.Store
                        let r' = ps'.Store
                        let q  = ps.State
                        match l with
                        | Noop (x, (ValM Star, s')) -> 
                            let s1' = Store.trim (Map.union s' r') z0
                            let z1  = Map.domain s1'
                            let z1' = Set.intersect (Set.union (Map.domain r) x) z1
                            let r'' = Map.filter (fun k _ -> Set.contains k z1') s1'
                            let targetState = 
                              if (snd s.[rk']).["val"] = VNum 0 then
                                c2s.[s1'].InitS
                              else
                                c1s.[s1'].InitS
                            let newTrans = SetT (ps, Set.difference z1 (Map.domain r''), targetState)
                            newC1sTrans := newTrans :: !newC1sTrans
                        | _ -> failwith "Expected noop with star label"
                    | _ -> failwith "Expected pair state from nu construction"
                | _ -> failwith "Expected pair state from nu construction"
           let aStates = c1sStates @ c2sStates
           let iState  = c1s.[s].InitS
           let fStates = Set.toList <| List.fold (fun xs t -> Set.add (getSecondState t) xs) Set.empty c2sFinals
           let transs  = c2sTrans @ c2sFinals @ !newC1sTrans
           let owner   = Map.fold (fun owner _ (a:Automaton) -> Map.union a.Owner owner) Map.empty c1s
           let owner'  = Map.fold (fun owner' _ (a:Automaton) -> Map.union a.Owner owner') owner c2s
           let rank   = Map.fold (fun rank _ (a:Automaton) -> Map.union a.Rank rank) Map.empty c1s
           let rank'  = Map.fold (fun rank' _ (a:Automaton) -> Map.union a.Rank rank') rank c2s
           {
             States   = aStates
             Owner    = owner'
             InitS    = iState
             TransRel = transs
             Rank     = rank'
             Final    = fStates
             InitR    = Set.toList x0
           }
    

//  and fromCanLet (d: TyEnv) (g: ITbl) (c: CanLet) (l: Label) : Automaton =
//    match c with
//    | Skip -> 
