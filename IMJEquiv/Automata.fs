namespace IMJEquiv
open IMJEquiv
open System

type State =
  inherit IComparable

[<CustomComparison>]
[<StructuralEquality>]
[<StructuredFormatDisplayAttribute("{Show}")>]
type IntState =
  {
    Val : Int
  }

  interface State with
    override x.CompareTo (yobj: Object) : Int =
      match yobj with
      | :? IntState as y -> compare x.Val y.Val  
      | _ -> 1

  override x.ToString () =
    x.Val.ToString ()

  member x.Show = x.ToString ()

[<CustomComparison>]
[<StructuralEquality>]
[<StructuredFormatDisplayAttribute("{Show}")>]
type PairState =
  {
    State : State
    Store : Store
  }
  
  interface State with
    member x.CompareTo (yobj: Object) : Int =
      match yobj with
      | :? PairState as y -> compare (x.State, x.Store) (y.State, y.Store)
      | _ -> -1

  override x.ToString () =
    sprintf "(%O, %A)" x.State x.Store

  member x.Show = x.ToString ()

type Label = Move * Store

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

  let labelOfTLabel (t: TransLabel) : Label =
    match t with
    | Push (_,l,_,_) 
    | Pop  (_,l,_,_,_)
    | Noop (_,l)       -> l

  let getSndState (t: Transition) : State =
    match t with
    | SetT (_,_,q)
    | PermT (_,_,q)
    | LabelT (_,_,q) -> q

  let getFstState (t: Transition) : State =
    match t with
    | SetT (q,_,_)
    | PermT (q,_,_)
    | LabelT (q,_,_) -> q


  /// Given an automaton `a`, `prune a` is the sub-automaton of
  /// `a` consisting only of reachable structure
  let prune (a: Automaton) : Automaton =
    // Implemented with a hashset due to efficiency problem
    let rqs = HashSet ()
    let addSuccs (acc: List<State>) (q: State) = 
      let addNew (acc: List<State>) (t: Transition) : List<State> =
        if getFstState t = q then
          let q' = getSndState t
          if not (rqs.Contains q') then (ignore (rqs.Add q'); q'::acc) else acc
        else
          acc
      List.fold addNew acc a.TransRel
    // List `frontier` is always a subset of rqs
    let rec reachable (frontier : List<State>) : Unit =
      match frontier with
      | [] -> ()
      | _::_ ->
          let frontier' = List.fold addSuccs [] frontier
          reachable frontier'

    let _ = rqs.Add a.InitS
    let _ = reachable [a.InitS]
    let rts = List.filter (fun t -> rqs.Contains (getFstState t)) a.TransRel
    let rfs = List.filter (fun q -> rqs.Contains q) a.Final
    let row = Map.restrict a.Owner (Set.ofSeq rqs)
    let rrk = Map.restrict a.Rank (Set.ofSeq rqs)
    {
      Automaton.Final    = rfs
      Automaton.InitR    = a.InitR
      Automaton.InitS    = a.InitS
      Automaton.Owner    = row
      Automaton.Rank     = rrk
      Automaton.States   = List.ofSeq rqs
      Automaton.TransRel = rts
    }

  let labelOfTrans (t: Transition) : Option<Label> =
    match t with
    | LabelT (_, tl, _) ->
        match tl with
        | Push (_, l, _, _)
        | Pop  (_, l, _, _, _)
        | Noop (_, l)       -> Some l
    | _                 -> None
   
  let muSupp (ms: List<Move>) : Set<RegId> =
    List.fold (fun acc m -> Set.union acc (Move.supp m)) Set.empty ms

  let labelSupp ((m,s): Label) : Set<RegId> =
    Set.union (Move.supp m) (Store.supp s)

  let private stateCount = ref 0

  let newState () : State =
    do stateCount := !stateCount + 1
    { Val = !stateCount } :> State

  let empty (s0: Store) : Automaton =
    let initState = newState ()
    {
      States = [initState]
      InitS = initState
      Owner = Map.singleton initState P
      TransRel = []
      InitR = []
      Final = []
      Rank = Map.singleton initState s0
    } 

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


  let toDot (a: Automaton) : String =
    let storeLabel = ref 0
    let storeTable = HashMap ()
    let permLabel = ref 0
    let permTable = HashMap ()
    let printSet (xs: Seq<'A>) : String = 
      List.toStringWithDelims "{" "," "}" (Seq.toList  xs)
    // Rather than printing every store in full,
    // print a label for the store of the form `si`
    let printStore (s: Store) : String =
      let i = 
        match HashMap.tryFind s storeTable with
        | Some i -> i
        | None -> 
            do incr storeLabel
            do storeTable.[s] <- !storeLabel
            !storeLabel
      "s" + i.ToString ()
    // Rather than printing every permutation in full,
    // print a label for the permutation of the form `pi`
    let printPerm (p: Perm<RegId>) : String =
      let i = 
        match HashMap.tryFind p permTable with
        | Some i -> i
        | None -> 
            do incr permLabel
            do permTable.[p] <- !permLabel
            !permLabel
      "p" + i.ToString ()
    let rec printState (q: State) : String =
      match q with
      | :? IntState as p -> "q" + p.Val.ToString ()
      | :? PairState as p -> printState p.State + printStore p.Store 
    let printStateDecl (q: State) : String =
      let shape = if List.contains q a.Final then "doublecircle" else "circle"
      let rec printLabel (q: State) = 
        match q with
        | :? IntState as p -> "q" + p.Val.ToString ()
        | :? PairState as p -> "(" + printLabel p.State + ", " + printStore p.Store + ")"
      let qstr = printLabel q
      sprintf "%s [label=\"%s[%s]\",shape=%s]" (printState q) qstr (printStore a.Rank.[q]) shape
    let printStateDecls () : String =
      List.fold (fun s q -> s + printStateDecl q + "\n") "" a.States
    let printTransition (t: Transition) : String =
      match t with
      | Transition.SetT (q, rs, q') -> sprintf "%s -> %s [label=\"%s\"]" (printState q) (printState q') (printSet rs)
      | Transition.PermT (q, pi, q') -> sprintf "%s -> %s [label=\"%s\"]" (printState q) (printState q') (printPerm pi)
      | Transition.LabelT (q, tl, q') -> 
          let tls =
            match tl with
            | TransLabel.Noop (x, (m, s)) -> sprintf "nu %s. %A[%s]" (printSet x) m (printStore s)
            | TransLabel.Pop (x, (m, s), q'', y, z) -> sprintf "nu %s. %A[%s] / %s, %s, %s" (printSet x) m (printStore s) (printState q'') (printSet y) (printSet z)
            | TransLabel.Push (x, (m, s), q'', y) -> sprintf "nu %s. %A[%s] \\ %s, %s" (printSet x) m (printStore s) (printState q'') (printSet y)
          sprintf "%s -> %s [label=\"%s\"]" (printState q) (printState q') tls
    let printTransitions () : String =
      List.fold (fun s t -> s + printTransition t + "\n") "" a.TransRel
    let printStoreContents (m: Store) : String =
      let printFieldContents (m: Map<FldId,Val>) : String =
        Map.fold (fun ss k v -> "\l\t\t" + k.ToString () + " = " + v.ToString()) "" m
      Map.fold (fun ss k (i,m') -> ss + "\l\t" + k.ToString() + " : " + i + printFieldContents m') "" m
    let printStoreTable () : String =
      let str = ref ""
      for k in storeTable.Keys do
        str := !str + "\ls" + storeTable.[k].ToString () + ": " + k.ToString ()
      sprintf "\nstores [label=\"%s\", shape=box]" !str
    let printPermTable () : String =
      let str = ref ""
      for k in permTable.Keys do
        str := !str + "\np" + permTable.[k].ToString () + ": " + k.ToString ()
      sprintf "\nperms [label=\"%s\", shape=box]" !str    
    sprintf "digraph automaton {\n" + printStateDecls () + printTransitions () + printStoreTable () + printPermTable () + "}"


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
              let _, cod = Store.splitSupp (Map.filter (fun k _ -> not (Map.containsKey k r)) a.Rank.[q])
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
                let domR' = Map.domainList r'
                let addMaplet (m: Store) (i:RegId) =
                  match Map.tryFind i a.Rank.[qp'] with
                  | None -> m
                  | Some v -> Map.add i v m
                let r'' = List.fold addMaplet Map.empty domR'
                let x' = Set.difference x domR
                let qpr = { State = qp; Store = r } :> State
                let qp'r'' = { State = qp'; Store = r'' } :> State
                let acc' = Set.add (SetT (qpr, x', qp'r'')) acc
                let newrs' = if Set.contains r'' rs then newrs else Set.add r'' newrs
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
      let ranker m (q,r) = Map.add ({ State = q; Store = r } :> State) (Map.filter (fun k _ -> not <| Map.containsKey k r) a.Rank.[q]) m
      Set.fold ranker Map.empty stPairs
    let finals = Set.fold (fun xs (q,r) -> if List.contains q a.Final then { State = q; Store = r } :> State :: xs else xs) [] stPairs
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
 

  type Call = State * Set<RegId> * RegId * MethId * List<Val> * Store * State
  type Ret  = Set<RegId> * Val * Store * State
  type CallRet = Call * Ret

  let partitionCallRets (rk: RegId) (owner: Map<State,Player>) (trs: List<Transition>) : Map<Call, List<Ret>> * List<Transition> =
     let hs = HashSet ()
     List.iter (fun tr -> ignore (hs.Add tr)) trs
     let findRets (q': State) (ri: RegId) (mth: MethId) : List<Ret> =
       let isRet (tr: Transition) : Option<Ret> =
         match tr with
         | LabelT (q1, Noop (x', (Ret (ri', mth', v),s')), q2) when ri' = ri && mth' = mth && q1 = q' -> Some (x',v,s',q2)
         | _ -> None
       List.fold (fun rs tr -> match isRet tr with Some ret -> let _ = hs.Remove tr in ret::rs | None -> rs) [] trs
     let doCall (acc: Map<Call,List<Ret>>) (tr: Transition) : Map<Call,List<Ret>> =
       match tr with
       | LabelT (q1, Noop (x, (Call (ri, mth, vs),s)), q2) when owner.[q1] = P && ri <> rk -> 
           let _ = hs.Remove tr
           let rets = findRets q2 ri mth
           Map.add (q1, x, ri, mth, vs, s, q2) rets acc
       | _ -> acc
     let callrets = List.fold doCall Map.empty trs
     (callrets, Seq.toList hs)

  let alphaEq (fxd: Set<RegId>) (tl1: TransLabel) (tl2: TransLabel) : Bool =
    
    let aEq (fxd: Set<RegId>) (m1, s1) (m2, s2) : Option<Perm<RegId>> =
      let r = -1
      match m1, m2 with
      | Call (r1, mth1, ls1), Call (r2, mth2, ls2) ->
          if mth1 = mth2 then
            let fldMap1, _ = List.fold (fun (m,i) l -> (Map.add (i.ToString ()) l m, i+1)) (Map.empty,0) (VReg r1 :: ls1)
            let fldMap2, _ = List.fold (fun (m,i) l -> (Map.add (i.ToString ()) l m, i+1)) (Map.empty,0) (VReg r2 :: ls2)
            let s1' = Map.add r ("_fake", fldMap1) s1
            let s2' = Map.add r ("_fake", fldMap2) s2
            Store.alphaEq (Set.add r fxd) s1' s2' 
          else
            None
      | Ret (r1, mth1, v1), Ret (r2, mth2, v2) ->
          if mth1 = mth2 then
            let fldMap1 = Map.ofList [("0", VReg r1); ("1", v1)]
            let fldMap2 = Map.ofList [("0", VReg r2); ("1", v2)] 
            let s1' = Map.add r ("_fake", fldMap1) s1
            let s2' = Map.add r ("_fake", fldMap2) s2
            Store.alphaEq (Set.add r fxd) s1' s2' 
          else
            None
      | ValM  v1, ValM v2 ->
            let fldMap1 = Map.ofList [("0", v1)]
            let fldMap2 = Map.ofList [("0", v2)] 
            let s1' = Map.add r ("_fake", fldMap1) s1
            let s2' = Map.add r ("_fake", fldMap2) s2
            Store.alphaEq (Set.add r fxd) s1' s2' 
      | _, _ -> None

    let optPerm = 
      match tl1, tl2 with
      | Noop (_, l1), Noop (_, l2) -> 
          aEq fxd l1 l2
      | Pop (x1, l1, sc1, y1, z1), Pop (x2, l2, sc2, y2, z2) -> 
          failwith ""
      | Push (x1, l1, sc1, z1), Push (x2, l2, sc2, z2) ->
          failwith ""
      | _, _ -> None
    Option.isSome optPerm

  let rec mkMethodsAutomaton (d: ITbl) (g: TyEnv) (x: Ident) (rk: RegId) (i: IntId) (mu: List<Move>) (tyZ0: Set<RegId * IntId>) (mths: List<CanMeth>) = 
    let tyZ0' = Set.add (rk, i) tyZ0 
    let z0' = Set.map fst tyZ0'
    let ss = Store.stores d Set.empty tyZ0'
    let tyMths = ITbl.methods d i
    let unionOfStores = List.fold (fun tySpp st -> Set.union tySpp (Store.tySupp d st)) Set.empty ss
    let mkMethodInits (mth: CanMeth) : List<List<Val> * Store> =
      let fldcnt = ref 0
      let _, argTys, retTy = List.find (fun (mid,_,_) -> mid = mth.Name) tyMths
      let fldMap = List.fold (fun m ty -> fldcnt := !fldcnt + 1; Map.add (fldcnt.ToString()) (IFld ty) m) Map.empty argTys
      let ifaceDfn = Eqn fldMap
      let d' = Map.add "__fake" ifaceDfn d
      let r = -1
      let mss = Store.stores d' unionOfStores (Set.add (r, "__fake") tyZ0')
      let mapper (st:Store) =
        let _, fldMap = st.[r]
        let orderedFlds = Seq.sortBy (fun (k, v) -> Int32.Parse k) (Map.toSeq fldMap)
        let ls = Seq.map snd orderedFlds
        let str = Map.remove r st
        (Seq.toList ls, str)
      List.map mapper mss
    let qfs = HashMap ()
    List.iter (fun st -> let qf = newState () in qfs.[st] <- qf) ss
    let cPhis = HashMap ()
    let mkCAuto (l: List<Val>) (st: Store) (mth: CanMeth) =
      let _, argTys, retTy = List.find (fun (mid,_,_) -> mid = mth.Name) tyMths
      let mu' = mu @ (ValM (VReg rk) :: List.map (fun x -> ValM x) l)
      let g'  = g @ ((x, Iface i) :: List.map2 (fun a ty -> (a, ty)) mth.Vars argTys)
      let ci  = fromCanon d g' mth.Body mu' st 
      ci
    let mkCPhis (mth: CanMeth) =
      let lsSs = mkMethodInits mth
      List.iter (fun (l,st) -> cPhis.[(mth.Name,l,st)] <- mkCAuto l st mth) lsSs  
    List.iter mkCPhis mths
    let accTrans = ref []
    let accOwner = ref Map.empty
    let accRank  = ref Map.empty
    // Construct (initial) opponent calls
    for st in ss do
      let newTranss = ref []
      let qf = qfs.[st]
      do accOwner := Map.add qf O !accOwner
      do accRank := Map.add qf st !accRank
      for kvp in cPhis do
        let mthName,ls,st' = kvp.Key
        let ci = kvp.Value
        let y = Map.domain st'
        let fxd = Map.domain st
        let x = Set.difference y fxd
        let newTl = Noop (x, (Call (rk,mthName,ls), st'))
        let newTrans = LabelT (qf, newTl, ci.InitS)
        let isAEq = List.exists (fun t -> match t with LabelT (_,tl,_) -> alphaEq fxd tl newTl | _ -> false) !newTranss
        if not (isAEq) then newTranss := newTrans :: !newTranss
      accTrans := !accTrans @ !newTranss
    // Construct (initial) player returns
    for kvp in cPhis do
      let mthName,ls,st' = kvp.Key
      let ci = kvp.Value
      do accOwner := Map.union ci.Owner !accOwner
      do accRank := Map.union ci.Rank !accRank
      let ftrans, rest = List.partition (fun tr -> isFinalTrans ci tr) ci.TransRel
      for tr in ftrans do
        match tr with
        | LabelT (q, Noop (x, (ValM l, s'')), qf) -> 
            let sj' = Store.trim s'' z0'
            let z = Map.domain sj'
            let q' = newState ()
            let q'' = newState ()
            do accOwner := Map.add q'' O (Map.add q' O !accOwner)
            do accRank := Map.add q'' (Map.restrict s'' z) (Map.add q' s'' !accRank)
            let qq' = LabelT (q, Noop (x, (Move.Ret (rk, mthName, l), s'')), q')
            let q'q'' = SetT (q', z, q'')
            let sj, pi = Store.findWithWitness z0' sj' ss
            let q''qfsj = PermT (q'', pi, qfs.[sj])
            accOwner := Map.remove qf !accOwner
            accRank  := Map.remove qf !accRank
            accTrans := qq' :: q'q'' :: q''qfsj :: !accTrans
        | _ -> failwith "Expected labelled noop value transition as final transition"
      // Construct push transitions
      let callRets, rest' = partitionCallRets rk ci.Owner rest
      do accTrans := rest' @ !accTrans // at this point rest' remain untouched
      for crp in callRets do
        let (q, x, ri, mth, ls, s'', q') = crp.Key 
        let sj' = Store.trim s'' z0'
        let z = Map.domain sj'
        let y = Map.domain s''
        let qin = newState ()
        let qin' = newState ()
        do accOwner := Map.add qin' O (Map.add qin O !accOwner)
        do accRank := Map.add qin' (Map.restrict s'' z) (Map.add qin s'' !accRank)
        let qqin = LabelT (q,Push (x,(Call (ri,mth,ls), s''),q',y),qin)
        let qinqin' = SetT (qin,z,qin')
        let sj, pi = Store.findWithWitness z0' sj' ss
        let qin'qfsj = PermT (qin', pi, qfs.[sj])
        accTrans := qqin :: qinqin' :: qin'qfsj :: !accTrans
        // Construct pop transitions
        for (x', l', s', q'') in crp.Value do
          for st in ss do
            let domSj' = Map.domain st
            let fs = Perm.allPartialPerms z0' domSj' (Set.union x' y)
            let sz = Set.count domSj'
            let extend (f: Perm<RegId>) : Perm<RegId> =
              let codf = Map.codomain f
              let szCodf = Set.count codf
              let remCod = Store.nextiReg (sz-szCodf) (Set.union x' y)
              let remDom = Set.difference domSj' (Map.domain f)
              Perm.extendPartial f (Set.toList remDom) (Set.toList remCod)
            let qfsj' = qfs.[st]
            for f in fs do
              let qint = newState ()
              let pi = extend f
              do accOwner := Map.add qint O !accOwner
              do accRank  := Map.add qint (Store.postPermute pi st) !accRank
              let qfsj'qint = PermT (qfsj', pi, qint)
              let codf = Map.codomain f
              let x'' = Set.difference x' codf
              let y' = Set.intersect y codf
              let qintq'' =  LabelT (qint,Pop (x'',(Ret (ri,mth,l'),s'),q',y,y'),q'')
              accTrans := qfsj'qint :: qintq'' :: !accTrans
    (!accTrans, !accRank, !accOwner, qfs, ss)

  and fromCanon (d: ITbl) (g: TyEnv) (cn: Canon) (mu: List<Move>) (s: Store) : Automaton =
    let x0 = Map.domain s
    let z0 = muSupp mu
    let automaton = 
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
      | Let (z, Assn (x,f,y), c) ->
          let rk', v = 
            match mu.[Types.getPosInTyEnv x g] with
            | ValM (VReg rk') -> 
                match mu.[Types.getPosInTyEnv y g] with
                | ValM v -> rk', v
                | _ -> failwith "Expected assignment value to be a value."
            | _ -> failwith "Expected assignment variable to be a register."
          let newStore = Store.update s rk' f v
          let trimmedStore = Store.trim newStore (muSupp mu)
          let g' = g @ [(z,Ty.Void)]
          let mu' = mu @ [ValM VStar]
          let cAuto = fromCanon d g' c mu' trimmedStore
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
          let mu' = List.append mu  [ValM VNul]
          let g' = List.append g [(x, ty)]
          let cAuto = fromCanon d g' c mu' s
          cAuto
       | Let (x, CanLet.Num i, c) ->
          let mu' = List.append mu  [ValM (VNum i)]
          let g' = List.append g [(x, Int)]
          let cAuto = fromCanon d g' c mu' s
          cAuto
       | Let (x, Skip, c) ->
          let mu' = List.append mu  [ValM VStar]
          let g' = List.append g [(x, Ty.Void)]
          let cAuto = fromCanon d g' c mu' s
          cAuto
       | Let (x, Plus (y,z), c) ->
          let (ValM (VNum yval)) = mu.[Types.getPosInTyEnv y g]
          let (ValM (VNum zval)) = mu.[Types.getPosInTyEnv z g]
          let mu' = List.append mu  [ValM (VNum (yval + zval))]
          let g' = List.append g [(x, Int)]
          let cAuto = fromCanon d g' c mu' s
          cAuto
       | Let (y, Eq (x1, x2), c) -> 
          let cmp = 
            match mu.[Types.getPosInTyEnv x1 g], mu.[Types.getPosInTyEnv x2 g] with
            | ValM (VNum i), ValM (VNum j) -> if i = j then 1 else 0
            | ValM (VReg x1val), ValM (VReg x2val) -> if x1val = x2val then 1 else 0
            | ValM VNul, ValM VNul -> 1
            | _, _ -> 0
          let mu' = List.append mu  [ValM (VNum cmp)]
          let g' = List.append g [(y, Int)]
          let cAuto = fromCanon d g' c mu' s
          cAuto
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
          let (ValM (VReg rk')) = mu.[Types.getPosInTyEnv x g]
          let (i,m) = s.[rk']
          let v  = m.[f]
          let ty = Types.ofFld d i f 
          let mu' = List.append mu  [ValM v]
          let g' = List.append g [(y, ty)]
          let cAuto = fromCanon d g' c mu' s
          cAuto
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
                let allStores = Store.stores d (Store.tySupp d s) tyZ0
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
                  let allStores = Store.stores d (Store.tySupp d s) tyZ0'
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
                let allStores = Store.stores d (Store.tySupp d s) tyZ0
                let s0'folder (states, owner, rank, trel, final) s0' =
                  let (nuX, rY) = getPair s0'
                  let jfolder (states', owner', rank', trel', final') j =
                    let mu' = List.append mu [ValM (VNum j)]
                    let g'  = List.append g [(x, xty)]
                    let autoc = fromCanon d g' c mu' s0'
                    let q' = newState ()
                    let ret1 = LabelT (q1, Noop (nuX, (Ret (rj,m,VNum j), s0')), q')
                    let ret2 = SetT (q', rY, autoc.InitS)
                    let states'' = q' :: states' @ autoc.States
                    let owner'' = Map.union (Map.add q' P owner') autoc.Owner 
                    let rank'' = Map.union (Map.add q' s0' rank') autoc.Rank
                    let trel'' = [ret1; ret2] @ trel' @ autoc.TransRel
                    let final'' = final' @ autoc.Final
                    (states'', owner'', rank'', trel'', final'')
                  let js = [0..Val.maxint]
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
       | Let (z, While (r, c1), c2) -> 
           let (ValM (VReg rk')) = mu.[Types.getPosInTyEnv r g]
           if (snd s.[rk']).["val"] = VNum 0 then
             fromCanon d g c2 mu s
           else
             let z0 = muSupp mu
             let tyZ0 = Set.map (fun r -> (r, Store.tyOfReg s r)) z0
             let allStores = Store.stores d (Store.tySupp d s) tyZ0
             let mkNuC1 c s1 =
               let c'  = fromCanon d g c mu s1
               nu d c' Map.empty 
             let mkNuC2 c s1 =
               let g'  = g @ [(z,Ty.Void)]
               let mu' = mu @ [Move.ValM Val.VStar]
               let c'  = fromCanon d g' c mu' s1
               nu d c' Map.empty 
             let c1s = List.fold (fun c1s str -> Map.add str (mkNuC1 c1 str) c1s) Map.empty allStores
             let c2s = List.fold (fun c2s str -> Map.add str (mkNuC2 c2 str) c2s) Map.empty allStores
             let mkTuple (qs, nfts, fts) (a: Automaton) =
               let nfts', fts' = List.partition (not << isFinalTrans a) a.TransRel
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
                          | Noop (x, (ValM VStar, s')) -> 
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
             let fStates = Set.toList <| List.fold (fun xs t -> Set.add (getSndState t) xs) Set.empty c2sFinals
             let transs  = c2sTrans @ c2sFinals @ !newC1sTrans
             let owner   = Map.fold (fun owner _ (a:Automaton) -> Map.union owner a.Owner) Map.empty c1s
             let owner'  = Map.fold (fun owner' _ (a:Automaton) -> Map.union owner' a.Owner ) owner c2s
             let rank   = Map.fold (fun rank _ (a:Automaton) -> Map.union rank a.Rank) Map.empty c1s
             let rank'  = Map.fold (fun rank' _ (a:Automaton) -> Map.union rank' a.Rank) rank c2s
             {
               States   = aStates
               Owner    = owner'
               InitS    = iState
               TransRel = transs
               Rank     = rank'
               Final    = fStates
               InitR    = Set.toList x0
             }
       | NewR (oi',x,i,mths) ->
           match oi' with
           | Some i' when not (Types.subtype d i i') ->
               empty s
           | _ ->
               let rk = Store.nextReg x0
               let tyZ0 = Set.map (fun r -> (r, Store.tyOfReg s r)) z0
               let z0' = Set.add rk z0
               let trans, rank, owner, qfs, ss = mkMethodsAutomaton d g x rk i mu tyZ0 mths  
               let s1 = Map.add rk (i, Store.mkDefaultObj d i) s
               let s1', pi1 = Store.findWithWitness z0' s1 ss
               let q0 = newState ()
               let q0' = newState ()
               let q0q0' = LabelT (q0, Noop (Set.singleton rk, (ValM (VReg rk), s1)) ,q0')
               let q1 = qfs.[s1']
               let q0'q1 = PermT (q0',pi1,q1)
               let owner' = Map.add q0 P (Map.add q0' O owner)
               let rank'  = Map.add q0 s (Map.add q0' s1 rank)
               let trans' = q0q0' :: q0'q1 :: trans
               {
                 Automaton.Final = List.map (fun s -> qfs.[s]) ss
                 Automaton.InitR = Set.toList x0
                 Automaton.InitS = q0
                 Automaton.Owner = owner'
                 Automaton.Rank = rank'
                 Automaton.States = q0 :: List.map getSndState trans'
                 Automaton.TransRel = trans'
               } 
       | Let (x, NewB (x',i,mths), c') ->
           let rk = Store.nextReg x0
           let tyZ0 = Set.map (fun r -> (r, Store.tyOfReg s r)) z0
           let z0' = Set.add rk z0
           let psi0 = Store.mkDefaultObj d i
           let r0 = Map.singleton rk (i, psi0)
           let g' = g @ [(x,Ty.Iface i)]
           let mu' = mu @ [ValM (VReg rk)]
           let s0' = Map.union s r0
           let ac' = fromCanon d g' c' mu' s0' 
           let a' = nu d ac' r0
           let trans, rank, owner, qfs, ss = mkMethodsAutomaton d g x' rk i mu tyZ0 mths
           let ftrans, rest = List.partition (fun tr -> isFinalTrans a' tr) a'.TransRel
           let accTrans = ref (trans @ rest)
           let accOwner = ref (Map.union owner a'.Owner)
           let accRank = ref (Map.union rank a'.Rank)
           for tr in ftrans do
            match tr with
            | LabelT (q, Noop (x, (ValM (VReg r), s'')), qf) when r = rk -> 
                let sj' = Store.trim s'' z0'
                let z = Map.domain sj'
                let q' = newState ()
                let q'' = newState ()
                do accOwner := Map.add q'' O (Map.add q' O !accOwner)
                do accRank := Map.add q'' (Map.restrict s'' z) (Map.add q' s'' !accRank)
                let qq' = LabelT (q, Noop (x, (ValM (VReg r), s'')), q')
                let q'q'' = SetT (q', z, q'')
                let sj, pi = Store.findWithWitness z0' sj' ss
                let q''qfsj = PermT (q'', pi, qfs.[sj])
                accTrans := qq' :: q'q'' :: q''qfsj :: !accTrans
            | _ -> accTrans := tr :: !accTrans
           {
             Automaton.Final = a'.Final @ (Seq.toList qfs.Values)
             Automaton.InitR = a'.InitR
             Automaton.InitS = a'.InitS
             Automaton.Owner = !accOwner
             Automaton.Rank = !accRank
             Automaton.States = a'.InitS :: List.map getSndState !accTrans
             Automaton.TransRel = !accTrans
           }
    let pruned = prune automaton  
    pruned
    
    
  let numRegs (a: Automaton) : Int =
    let doTrans regs t =
      match labelOfTrans t with
      | None -> regs
      | Some l ->
          let rs = labelSupp l
          Set.union regs rs
    let regs = 
      List.fold doTrans Set.empty a.TransRel
    Set.count regs
