// This file defines IMJ Automata (IMJA) and the translation from 
// canonical forms to IMJA.

namespace IMJEquiv
open System

/// IMJ Automaton states are either
/// simple integers, or pairs of 
/// state and some hidden store.
type IMJAState =
  | Simple of int
  | Hiding of IMJAState * Store

  override x.ToString () =
    match x with
    | Simple i -> i.ToString ()
    | Hiding (q,s) -> sprintf "(%O,%O)" q s

/// Symbolic representation of letters from
/// the infinite alphabet is a pair of 
/// (symbolic) move and (symbolic) store.
type Letter = Move * Store

/// Constants to be stored on the stack
/// are IMJ automaton states.
type StackConst = IMJAState

/// Transitions representing moves (those with a letter) 
/// can be partitioned into pushes, pops and noops.
type MoveLabel =
  | PushL of Set<RegId> * Letter * StackConst * Set<RegId>
  | PopL  of Set<RegId> * Letter * StackConst * Set<RegId> * Set<RegId>
  | NoopL of Set<RegId> * Letter

/// IMJA transitions are labelled by either
/// moves, sets of register ids 
/// (for restriction) or permutations of register ids
type IMJALabel =
  | MoveL of MoveLabel
  | SetL  of Set<RegId>
  | PermL of Perm<RegId>

/// IMJA transitions consist of a start and end
/// state and a label
type IMJATransition = {
    Start: IMJAState
    Label: IMJALabel
    End:   IMJAState
  }
 
/// Players are (P)roponent and (O)pponent
type Player =
  | O
  | P

/// The type of IMJ Automata
type IMJA =
 {
   States : List<IMJAState>
   Owner : Map<IMJAState,Player>
   InitS : IMJAState
   TransRel : List<IMJATransition>
   InitR : List<RegId>
   Final : List<IMJAState>
   Rank : Map<IMJAState,Store>
 }

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module IMJA = 

  /// Given a transition label for a move, returns the letter
  /// associated with that move.
  let letterOfTLabel (t: MoveLabel) : Letter =
    match t with
    | PushL (_,l,_,_) 
    | PopL  (_,l,_,_,_)
    | NoopL (_,l)       -> l

  /// Given a transition t, returns Some l if t is a move transition
  /// and l is the letter associated with the move; returns None otherwise.
  let letterOfTrans (t: IMJATransition) : Option<Letter> =
    match t.Label with
    | MoveL ml -> Some (letterOfTLabel ml)
    | _        -> None

  /// Given a transition, returns the end state
  let getSndState (t: IMJATransition) : IMJAState = t.End

  /// Given a transition, returns the start state
  let getFstState (t: IMJATransition) : IMJAState = t.Start

  /// Given an automaton a and a transition t, returns
  /// true just if the end state of t is a final state
  /// of a and returns false otherwise.
  let isFinalTrans (a: IMJA) (t: IMJATransition) : Bool =
    List.contains t.End a.Final

  /// Given a letter, returns its support.
  let letterSupp ((m,s): Letter) : Set<RegId> =
    Set.union (Move.supp m) (Store.supp s)

  let private stateCount = ref 0
  /// Returns a fresh state.
  let newState () : IMJAState =
    do stateCount := !stateCount + 1
    Simple !stateCount

  /// Given a set of registers fxd and two transition labels tl1 and tl2,
  /// returns true just if there is a permuation of register ids p which
  /// fixes registers in fxd and witnesses tl1 = p . tl2
  let alphaEq (fxd: Set<RegId>) (tl1: IMJALabel) (tl2: IMJALabel) : Bool =
    
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
      | MoveL (NoopL (_, l1)), MoveL (NoopL (_, l2)) -> 
          aEq fxd l1 l2
      | MoveL (PopL (x1, l1, sc1, y1, z1)), MoveL (PopL (x2, l2, sc2, y2, z2)) -> 
          failwith ""
      | MoveL (PushL (x1, l1, sc1, z1)), MoveL (PushL (x2, l2, sc2, z2)) ->
          failwith ""
      | _, _ -> None
    Option.isSome optPerm

  /// Given an automaton, returns the number of registers 
  /// used in its representation.
  let numRegs (a: IMJA) : Int =
    let doTrans regs t =
      match letterOfTrans t with
      | None -> regs
      | Some l ->
          let rs = letterSupp l
          Set.union regs rs
    let regs = 
      List.fold doTrans Set.empty a.TransRel
    Set.count regs

  /// Given an automaton `a`, `prune a` is the sub-automaton of
  /// `a` consisting only of reachable structure.
  let prune (a: IMJA) : IMJA =

    // List `frontier` is always a subset of rqs
    let rec reach (fst, snd) (pot: HashSet<IMJAState>) (fr: List<IMJAState>) : Unit =
      let rec fix fr = 
        if fr <> [] then
          let fr' = [
            for q in fr do
              for t in a.TransRel do
                let q1 = fst t
                let q2 = snd t
                if q1 = q && pot.Add q2 then yield q2
          ]
          fix fr'
      fix fr

    let fwdSeen  = HashSet [a.InitS]
    let fwdReach = reach (getFstState,getSndState) fwdSeen
    do ignore (fwdReach [a.InitS])

    let bwdSeen  = HashSet a.Final
    let bwdReach = reach (getSndState,getFstState) bwdSeen
    do ignore (bwdReach a.Final)

    // fwdSeen now contains all the live states
    do fwdSeen.IntersectWith bwdSeen

    let rts = List.filter (fun t -> fwdSeen.Contains (getFstState t) && fwdSeen.Contains (getSndState t)) a.TransRel
    let rfs = List.filter (fun q -> fwdSeen.Contains q) a.Final
    let liveSet = Set.ofSeq fwdSeen // To comply with Map.restrict's API
    let row = Map.restrict a.Owner liveSet
    let rrk = Map.restrict a.Rank liveSet
    {
      Final    = rfs
      InitR    = a.InitR
      InitS    = a.InitS
      Owner    = row
      Rank     = rrk
      States   = List.ofSeq fwdSeen
      TransRel = rts
    }
 

  /// Given an automaton a, returns a but with all loops of
  /// P-owned epsilon transitions replaced by *-move transitions 
  /// to a new "sink" state.
  let remPLoops (a: IMJA) : IMJA =

    let sink = newState ()

    /// Given a state q, returns Some ps where ps is the path of
    /// epsilon transitions connecting q to itself, if such a path
    /// exists and None otherwise.
    let epsLoop (q: IMJAState) : Option<List<IMJATransition>> =

      let applicable fr t =
        match t.Label with
          | SetL _
          | PermL _ when t.Start = fr -> true
          | _                         -> false

      // Given a current path out of q, a set hist of previously visited
      // states and a frontier state fr: returns Some ps if ps is an 
      // extension of path connecting q to itself via fr and None otherwise.
      // NOTE: this is essentially a breadth first search of the transition
      // graph restricted to paths from q made from epsilon transitions. 
      // Since q is owned by P and epsilon transitions are P->P all states
      // visited will be owned by P.  Since there is at most one epsilon
      // transition out of a P-state, it follows that the frontier of this
      // search is always a singleton, here: fr.
      let rec rea path hist fr =
        let t = List.tryFind (applicable fr) a.TransRel
        match t with
        | None -> None
        | Some t' ->
            let q2 = t'.End
            if q2 = q then
              Some (t' :: path)
            elif Set.contains q2 hist then
              None
            else 
              rea (t'::path) (Set.add q2 hist) q2

      rea [] (set [q]) q

    let loops = seq {
        for q in a.States do
          if a.Owner.[q] = P then
            match epsLoop q with
            | None -> ()
            | Some p -> yield (q, p)
      }
    
    let states = Seq.map fst loops
    let trans  = 
      Seq.fold (fun acc (_,p) -> List.fold (fun xs t -> Set.add t xs) acc p) Set.empty loops

    let mkNewTrans q = 
      let tl = NoopL (Set.empty, (ValM VStar, Map.empty))
      { Start=q; Label=MoveL tl; End=sink }

    let trans' = 
      Seq.fold (fun acc q -> (mkNewTrans q) :: acc) (List.filter (fun t -> not (Seq.contains t trans)) a.TransRel) states

    { 
      a with 
        States = sink :: a.States 
        TransRel = trans' 
        Owner = Map.add sink O a.Owner
        Rank = Map.add sink Map.empty a.Rank
    }


  /// Given an automaton, returns a string containing its representation
  /// in the DOT graph language.  
  let toDot (a: IMJA) : String =
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

    let rec printState (q: IMJAState) : String =
      match q with
      | Simple p     -> "q" + p.ToString ()
      | Hiding (p,s) -> printState p + printStore s

    let printStateDecl (q: IMJAState) : String =
      let shape = if List.contains q a.Final then "doublecircle" else "circle"
      let rec printLabel (q: IMJAState) = 
        match q with
        | Simple p     -> "q" + p.ToString ()
        | Hiding (p,s) -> "(" + printLabel p + ", " + printStore s + ")"
      let qstr = printLabel q
      sprintf "%s [label=\"%s[%s]\",shape=%s]" (printState q) qstr (printStore a.Rank.[q]) shape

    let printStateDecls () : String =
      List.fold (fun s q -> s + printStateDecl q + "\n") "" a.States

    let printTransition (t: IMJATransition) : String =
      let ls = 
        match t.Label with
        | SetL rs                             -> printSet rs
        | PermL pi                            -> printPerm pi
        | MoveL (NoopL (x, (m, s)))           -> sprintf "nu %s. %O[%s]" (printSet x) m (printStore s)
        | MoveL (PopL (x, (m, s), q'', y, z)) -> sprintf "nu %s. %O[%s] / %s, %s, %s" (printSet x) m (printStore s) (printState q'') (printSet y) (printSet z)
        | MoveL (PushL (x, (m, s), q'', y))   -> sprintf "nu %s. %O[%s] \\ %s, %s" (printSet x) m (printStore s) (printState q'') (printSet y)
      sprintf "%s -> %s [label=\"%s\"]" (printState t.Start) (printState t.End) ls

    let printTransitions () : String =
      List.fold (fun s t -> s + printTransition t + "\n") "" a.TransRel

    let printStoreContents (m: Store) : String =
      let printFieldContents (m: Map<FldId,Val>) : String =
        Map.fold (fun ss k v -> "\l\t\t" + k.ToString () + " = " + v.ToString()) "" m
      Map.fold (fun ss k (i,m') -> ss + "\l\t" + k.ToString() + " : " + i + printFieldContents m') "" m

    let printStoreTable () : String =
      let str = ref ""
      for k in storeTable.Keys do
        str := !str + "\ns" + storeTable.[k].ToString () + ": " + k.ToString ()
      sprintf "\nstores [label=\"%s\", shape=box]" !str

    let printPermTable () : String =
      let str = ref ""
      for k in permTable.Keys do
        str := !str + "\np" + permTable.[k].ToString () + ": " + k.ToString ()
      sprintf "\nperms [label=\"%s\", shape=box]" !str    
    sprintf "digraph automaton {\n" + printStateDecls () + printTransitions () + printStoreTable () + printPermTable () + "}"



  /// Given a store s0, returns the "empty" automaton 
  /// (whose only state is ranked by s0)
  let empty (s0: Store) : IMJA =
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

  /// Given a letter l, and stores s0 and sF, returns the automaton
  /// containing two fresh states q0 and qF ranked by s0 and sF
  /// respectively and linked by the move nu0.l.
  /// NOTE: It should be that snd l = sF.
  let twoStateAuto (l: Letter) (s0: Store) (sF: Store) : IMJA =
    let q0 = newState ()
    let qF = newState ()
    let owner = Map.ofList [(q0, P); (qF, O)]
    let rank = Map.ofList  [(q0, s0); (qF, sF)]
    let trans =
      { Start=q0; Label=MoveL (NoopL (Set.empty, l)); End=qF }
    {
      States = [q0; qF]
      Owner = owner
      InitS = q0
      TransRel = [trans]
      InitR = Set.toList (letterSupp l)
      Final = [qF]
      Rank = rank
    }


  /// Given an interface table d, an automaton a and a store r0, returns
  /// the automaton nu r0. a.
  let nu (_: ITbl) (a: IMJA) (r0: Store) : IMJA =

    // We follow the construction given in the paper, so consult that for further details.

    let q0' = Hiding (a.InitS,r0)
    
    let rec fix (ts: Set<IMJATransition>, rs: Set<Store>, frontier: Set<Store>) : Set<IMJATransition> * Set<Store> * Set<Store> =
      if Set.isEmpty frontier 
      then 
        (ts, rs, frontier) 
      else
        let folder (ts', rs', fs') (r: Store) =
          let mkTransFromTrans (acc: Set<IMJATransition>, newrs: Set<Store>) (t: IMJATransition) : Set<IMJATransition> * Set<Store> = 
            let domR = Map.domain r
            let inQ' q r = 
              let _, cod = Store.splitSupp (Map.filter (fun k _ -> not (Map.containsKey k r)) a.Rank.[q])
              (Map.isSubset r a.Rank.[q]) && Set.isEmpty (Set.intersect domR cod)
            match t.Label with
            | SetL x when a.Owner.[t.Start] = O && (inQ' t.Start r) ->
                let qo = t.Start
                let qo' = t.End
                if Set.isSubset domR x
                then
                  let x' = Set.difference x domR
                  let qor = Hiding (qo,r)
                  let qo'r = Hiding (qo',r)
                  let acc' = Set.add { Start=qor; Label=SetL x'; End=qo'r } acc
                  (acc', newrs)
                else 
                  (acc, newrs)
            | SetL x when a.Owner.[t.Start] = P && (inQ' t.Start r) ->
                let qp = t.Start
                let qp' = t.End
                let r' = Map.restrict r x
                let domR' = Map.domainList r'
                let addMaplet (m: Store) (i:RegId) =
                  match Map.tryFind i a.Rank.[qp'] with
                  | None -> m
                  | Some v -> Map.add i v m
                let r'' = List.fold addMaplet Map.empty domR'
                let x' = Set.difference x domR
                let qpr = Hiding (qp,r)
                let qp'r'' = Hiding (qp',r'')
                let acc' = Set.add { Start=qpr; Label=SetL x'; End=qp'r'' } acc
                let newrs' = if Set.contains r'' rs then newrs else Set.add r'' newrs
                (acc', newrs')
            | PermL pi when inQ' t.Start r ->
                let qo = t.Start
                let qo' = t.End
                let r' = Store.postPermute pi (Map.mapDom r (fun k -> pi.[k]))
                let qor = Hiding (qo,r)
                let qo'r = Hiding (qo',r')
                let tl = { Start=qor; Label=PermL pi; End=qo'r }
                let acc' = Set.add tl acc
                let newrs' = if Set.contains r' rs then newrs else Set.add r' newrs 
                (acc', newrs')
            | MoveL (PopL  (x, (mu, s), _, _, _)) 
            | MoveL (NoopL (x, (mu, s)))  when a.Owner.[t.Start] = O && (inQ' t.Start r) ->
                let qo = t.Start
                let qp' = t.End
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
                    let qor = Hiding (qo,r)
                    let qp'r = Hiding (qp',r)
                    let acc' = 
                      let tl' =
                        match t.Label with
                        | MoveL (PopL (_, _, q, y, z)) -> 
                            let newq = Hiding (q,r)
                            let y' = Set.difference y domR
                            let z' = Set.difference z domR
                            PopL  (x, (mu, sMinusR), newq, y', z')
                        | MoveL (NoopL  _) ->
                            NoopL (x, (mu, sMinusR))
                        | _ -> failwith "Impossible"
                      Set.add { Start=qor; Label=MoveL tl'; End=qp'r } acc
                    acc'
                  else 
                    acc
                (acc', newrs)
            | MoveL (PushL (x, (mu, s), _, _)) 
            | MoveL (NoopL (x, (mu, s))) when a.Owner.[t.Start] = P && (inQ' t.Start r) ->
                let qp = t.Start
                let qo' = t.End
                let qpr = Hiding (qp,r)
                let suppMu = Move.supp mu
                let domS = Map.domain s
                let domR = Map.domain r
                let zStore = Store.trim s (Set.union suppMu (Set.difference domS (Set.union x domR)))
                let z = Store.supp zStore
                let s' = Map.restrict s z
                let r' = Map.difference s s'
                let x' = Set.intersect (Set.union x domR) z
                let qo'r' = Hiding (qo',r')
                let tl' = 
                  match t.Label with
                  | MoveL (PushL (_, _, q, y)) ->
                      let newq = Hiding (q,r')
                      let y' = Set.difference y (Map.domain r')
                      PushL (x', (mu, s'), newq, y')
                  | MoveL (NoopL  _) -> NoopL (x', (mu, s')) 
                  | _ -> failwith "Impossible"
                let acc' = Set.add { Start=qpr; Label=MoveL tl'; End=qo'r' } acc
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
    let owner = Set.fold (fun m (q,r) -> Map.add (Hiding (q,r)) (a.Owner.[q]) m) Map.empty stPairs
    let rank =
      let ranker m (q,r) = Map.add (Hiding (q,r)) (Map.filter (fun k _ -> not <| Map.containsKey k r) a.Rank.[q]) m
      Set.fold ranker Map.empty stPairs
    let finals = Set.fold (fun xs (q,r) -> if List.contains q a.Final then Hiding (q,r) :: xs else xs) [] stPairs
    {
      States = Map.domainList owner
      Owner = owner
      InitS = q0'
      TransRel = Set.toList newts
      InitR = Set.toList (Set.difference (set a.InitR) (Map.domain r0))
      Final = finals
      Rank = rank
    }
      

  // For the purposes of making the methods automaton, it is useful to distinguish the
  // type of calls, returns and call-return pairs.
  type Call = IMJAState * Set<RegId> * RegId * MethId * List<Val> * Store * IMJAState
  type Ret  = Set<RegId> * Val * Store * IMJAState
  type CallRet = Call * Ret

  /// Given a register id rk, an ownership map owner and a list of transitions trs, returns the pair (m, ts)
  /// where m maps each call from a move in trs to the matching retursn in trs and ts is trs with all
  /// calls and their matching returns removed.
  let private partitionCallRets (rk: RegId) (owner: Map<IMJAState,Player>) (trs: List<IMJATransition>) : Map<Call, List<Ret>> * List<IMJATransition> =
     let hs = HashSet trs
     let findRets (q': IMJAState) (ri: RegId) (mth: MethId) : List<Ret> =
       let isRet (tr: IMJATransition) : Option<Ret> =
         match tr.Label with
         | MoveL (NoopL (x', (Ret (ri', mth', v),s'))) when ri' = ri && mth' = mth && tr.Start = q' -> Some (x',v,s',tr.End)
         | _ -> None
       List.fold (fun rs tr -> match isRet tr with Some ret -> let _ = hs.Remove tr in ret::rs | None -> rs) [] trs
     let doCall (acc: Map<Call,List<Ret>>) (tr: IMJATransition) : Map<Call,List<Ret>> =
       match tr.Label with
       | MoveL (NoopL (x, (Call (ri, mth, vs),s))) when owner.[tr.Start] = P && ri <> rk -> 
           let _ = hs.Remove tr
           let rets = findRets tr.End ri mth
           Map.add (tr.Start, x, ri, mth, vs, s, tr.End) rets acc
       | _ -> acc
     let callrets = List.fold doCall Map.empty trs
     (callrets, Seq.toList hs)

  let private dereference (m:Move) : Option<RegId> =
    match m with
    | ValM VNul ->     None
    | ValM (VReg r) -> Some r
    | _ -> failwith "Expected assignment variable to be a register or null."

  /// Given an interface table d, a type environment g, an identifier x, register id rk, interface i, methods mths and initial conditions (mu,s)
  /// returns an automaton representing the behaviour of an object with "this" identifier x and methods mths, stored in register id rk and 
  /// running from initial conditions (mu, s).
  let rec private mkMethodsAutomaton (d: ITbl) (g: TyEnv) (x: Ident) (rk: RegId) (i: IntId) (mths: List<CanMeth>) (mu: List<Move>) (s: Store) =
    // This is essentially the translation for the "new {...}" case according to the paper, without the initial state.
    // It has been moved out of that construction because the automatic representation of an object construction appears twice,
    // once in the "new {...}" case and once in the "let x = new {...}" case.  Our implementation follows the paper, see that for details.
    let z0 = Move.listSupp mu
    let tyZ0 = Set.map (fun r -> (r, Store.tyOfReg s r)) z0
    let tyZ0' = Set.add (rk, i) tyZ0 
    let z0' = Set.map fst tyZ0'
    let ss = Store.stores d Set.empty tyZ0'
    let tyMths = ITbl.methods d i
    let unionOfStores = List.fold (fun tySpp st -> Set.union tySpp (Store.tySupp d st)) Set.empty ss
    let mkMethodInits (mth: CanMeth) : List<List<Val> * Store> =
      let fldcnt = ref 0
      let _, argTys, retTy = List.find (fun (mid,_,_) -> mid = mth.Name) tyMths
      let fldMap = List.fold (fun m ty -> fldcnt := !fldcnt + 1; Map.add ((!fldcnt).ToString()) (IFld ty) m) Map.empty argTys
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
      let fxd = Map.domain st
      for kvp in cPhis do
        let mthName,ls,st' = kvp.Key
        let ci = kvp.Value
        let y = Map.domain st'
        let x = Set.difference y fxd
        let newTl = MoveL (NoopL (x, (Call (rk,mthName,ls), st')))
        let newTrans = {Start=qf; Label=newTl; End=ci.InitS}
//        let isAEq = List.exists (fun t -> alphaEq fxd t.Label newTl) !newTranss
//        if not (isAEq) then 
        newTranss := newTrans :: !newTranss
      accTrans := !accTrans @ !newTranss
    // Construct (initial) player returns
    for kvp in cPhis do
      let mthName,ls,st' = kvp.Key
      let ci = kvp.Value
      do accOwner := Map.union !accOwner ci.Owner
      do accRank := Map.union !accRank ci.Rank
      let ftrans, rest = List.partition (fun tr -> isFinalTrans ci tr) ci.TransRel
      for tr in ftrans do
        match tr.Label with
        | MoveL (NoopL (x, (ValM l, s''))) -> 
            let q = tr.Start
            let qf = tr.End
            let sj' = Store.trim s'' z0'
            let z = Map.domain sj'
            let q' = newState ()
            let q'' = newState ()
            do accOwner := Map.add q'' O (Map.add q' O !accOwner)
            do accRank := Map.add q'' (Map.restrict s'' z) (Map.add q' s'' !accRank)
            let qq' =  {Start=q; Label=MoveL (NoopL (x, (Move.Ret (rk, mthName, l), s''))); End=q'}
            let q'q'' = {Start=q'; Label=SetL z; End=q''}
            let sj, pi = Store.findWithWitness z0' sj' ss
            let q''qfsj = {Start=q''; Label=PermL pi; End=qfs.[sj]}
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
        let qqin = {Start=q; Label=MoveL (PushL (x,(Call (ri,mth,ls), s''),q',y)); End=qin}
        let qinqin' = {Start=qin; Label=SetL z; End=qin'}
        let sj, pi = Store.findWithWitness z0' sj' ss
        let qin'qfsj = {Start=qin'; Label=PermL pi; End=qfs.[sj]}
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
              // Extend the partial permutation to a full one:
              List.fold2 (fun p x y -> Map.add x y p) f (Set.toList remDom) (Set.toList remCod)
            let qfsj' = qfs.[st]
            for f in fs do
              let qint = newState ()
              let pi = extend f
              do accOwner := Map.add qint O !accOwner
              do accRank  := Map.add qint (Store.postPermute pi st) !accRank
              let qfsj'qint = {Start=qfsj'; Label=PermL pi; End=qint}
              let codf = Map.codomain f
              let x'' = Set.difference x' codf
              let y' = Set.intersect y codf
              let qintq'' =  {Start=qint; Label=MoveL (PopL (x'',(Ret (ri,mth,l'),s'),q',y,y')); End=q''}
              accTrans := qfsj'qint :: qintq'' :: !accTrans
    (!accTrans, !accRank, !accOwner, qfs, ss)

  /// Given an interface table, a type environment, a canonical form cn and initial conditions (mu, s),
  /// returns the automaton representing cn from (mu,s).
  and fromCanon (d: ITbl) (g: TyEnv) (cn: Canon) (mu: List<Move>) (s: Store) : IMJA =
    // The implementation follows the paper very closely, see that for more details.
    let x0 = Map.domain s
    let z0 = Move.listSupp mu
    let automaton = 
      match cn with
      | NullR -> twoStateAuto (ValM VNul, s) s s
      | Var x -> 
          let k = TyEnv.index x g
          twoStateAuto (mu.[k], s) s s
      | If (x, c1, c0) ->
          let k = TyEnv.index x g
          if mu.[k] = ValM (VNum 0) then
            fromCanon d g c0 mu s 
          else
            fromCanon d g c1 mu s
      | Let (z, Assn (x,f,y), c) ->
          let ork' = dereference (mu.[TyEnv.index x g])
          match ork' with
          | None -> empty s
          | Some rk' ->
              let v = Move.toValue (mu.[TyEnv.index y g])
              let newStore = Store.update s rk' f v
              let trimmedStore = Store.trim newStore (Move.listSupp mu)
              let g' = g @ [(z,Ty.Void)]
              let mu' = mu @ [ValM VStar]
              let cAuto = fromCanon d g' c mu' trimmedStore
              let q0 = newState ()
              let owner = Map.add q0 P cAuto.Owner 
              let rank = Map.add q0 s cAuto.Rank
              let trans = 
                { Start=q0; Label=SetL (Map.domain trimmedStore); End=cAuto.InitS }
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
          let yval = Move.toInt (mu.[TyEnv.index y g])
          let zval = Move.toInt (mu.[TyEnv.index z g])
          let mu' = List.append mu  [ValM (VNum (Val.add yval zval))]
          let g' = List.append g [(x, Int)]
          let cAuto = fromCanon d g' c mu' s
          cAuto
       | Let (x, Gre (y,z), c) ->
          let yval = Move.toInt (mu.[TyEnv.index y g])
          let zval = Move.toInt (mu.[TyEnv.index z g])
          let mu' = List.append mu  [ValM (VNum (if yval > zval then 1 else 0))]
          let g' = List.append g [(x, Int)]
          let cAuto = fromCanon d g' c mu' s
          cAuto
       | Let (y, Eq (x1, x2), c) -> 
          let cmp = 
            match mu.[TyEnv.index x1 g], mu.[TyEnv.index x2 g] with
            | ValM (VNum i), ValM (VNum j) -> if i = j then 1 else 0
            | ValM (VReg x1val), ValM (VReg x2val) -> if x1val = x2val then 1 else 0
            | ValM VNul, ValM VNul -> 1
            | _, _ -> 0
          let mu' = List.append mu [ValM (VNum cmp)]
          let g'  = List.append g [(y, Int)]
          let cAuto = fromCanon d g' c mu' s
          cAuto
       | Let (y, Cast (i, x), c) ->
           let ork' = dereference (mu.[TyEnv.index x g])
           match ork' with
           | None -> empty s
           | Some rk' ->
               let j, _ = s.[rk']
               if Type.subtype d j i then 
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
          let ork' = dereference (mu.[TyEnv.index x g])
          match ork' with
          | None -> empty s
          | Some rk' -> 
              let (i,m) = s.[rk']
              let v  = m.[f]
              let ty = Type.ofFld d i f 
              let mu' = List.append mu  [ValM v]
              let g' = List.append g [(y, ty)]
              let cAuto = fromCanon d g' c mu' s
              cAuto
       | Let (x, CanLet.Call (y,m,zs), c) ->
          let yi = Type.toInterface (TyEnv.lookup y g)
          let (_, xty) = Type.ofMeth d yi m
          let orj = dereference (mu.[TyEnv.index y g])
          match orj with
          | None -> empty s
          | Some rj ->
              let vs = List.map (fun z -> Move.toValue (mu.[TyEnv.index z g])) zs
              let q0 = newState ()
              let q1 = newState ()
              let callm = Call (rj, m, vs)
              let l = MoveL (NoopL (Set.empty, (callm, s)))
              let calltr = {Start=q0; Label=l; End=q1}

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
                    let z0 = Move.listSupp mu
                    let tyZ0 = Set.map (fun r -> (r, Store.tyOfReg s r)) z0
                    let allStores = Store.stores d (Store.tySupp d s) tyZ0
                    let folder (states, owner: Map<IMJAState,Player>, rank, trel, final) s0' =
                      let (nuX, rY) = getPair s0'
                      let mu' = List.append mu [ValM VStar]
                      let g'  = List.append g [(x, xty)]
                      let autoc = fromCanon d g' c mu' s0'
                      let q' = newState ()
                      let ret1 = {Start=q1; Label=MoveL (NoopL (nuX, (Ret (rj,m,VStar), s0'))); End=q'}
                      let ret2 = {Start=q'; Label=SetL rY; End=autoc.InitS}
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
                    let z0 = Move.listSupp mu
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
                        let ret1 = {Start=q1; Label=MoveL (NoopL (nuX, (Ret (rj,m,VReg rj'), s0'))); End=q'}
                        let ret2 = {Start=q'; Label=SetL rY; End=autoc.InitS}
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
                    let z0 = Move.listSupp mu
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
                        let ret1 = {Start=q1; Label=MoveL (NoopL (nuX, (Ret (rj,m,VNum j), s0'))); End=q'}
                        let ret2 = {Start=q'; Label=SetL rY; End=autoc.InitS}
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
           let rk' = Move.toRegister (mu.[TyEnv.index r g])
           if (snd s.[rk']).["_val"] = VNum 0 then
             fromCanon d g c2 mu s
           else
             let z0 = Move.listSupp mu
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
             let mkTuple (qs, nfts, fts) (a: IMJA) =
               let nfts', fts' = List.partition (not << isFinalTrans a) a.TransRel
               (qs @ a.States, nfts @ nfts', fts @ fts')
             let c1sStates, c1sTrans, c1sFinals = Set.fold mkTuple ([],[],[]) (Map.codomain c1s)
             let c2sStates, c2sTrans, c2sFinals = Set.fold mkTuple ([],[],[]) (Map.codomain c2s)
             let newC1sTrans = ref c1sTrans
             for t in c1sFinals do
               match t.Label with
               | MoveL (NoopL (x, (ValM VStar, s'))) ->
                   match t.Start with
                   | Hiding (q,r) ->
                       match t.End with
                       | Hiding (_,r') -> 
                           let s1' = Store.trim (Map.union s' r') z0
                           let z1  = Map.domain s1'
                           let z1' = Set.intersect (Set.union (Map.domain r) x) z1
                           let r'' = Map.filter (fun k _ -> Set.contains k z1') s1'
                           let targetState = 
                             if (snd s.[rk']).["_val"] = VNum 0 then
                               c2s.[s1'].InitS
                             else
                               c1s.[s1'].InitS
                           let newTrans = {Start=t.Start; Label=SetL (Set.difference z1 (Map.domain r'')); End=targetState}
                           newC1sTrans := newTrans :: !newC1sTrans
                       | _ -> failwith "Expected pair state from nu construction"
                   | _ -> failwith "Expected pair state from nu construction"
               | _ -> failwith "Expected noop with star label as final"
             let aStates = c1sStates @ c2sStates
             let iState  = c1s.[s].InitS
             let fStates = Set.toList <| List.fold (fun xs t -> Set.add (getSndState t) xs) Set.empty c2sFinals
             let transs  = c2sTrans @ c2sFinals @ !newC1sTrans
             let owner   = Map.fold (fun owner _ (a:IMJA) -> Map.union owner a.Owner) Map.empty c1s
             let owner'  = Map.fold (fun owner' _ (a:IMJA) -> Map.union owner' a.Owner ) owner c2s
             let rank   = Map.fold (fun rank _ (a:IMJA) -> Map.union rank a.Rank) Map.empty c1s
             let rank'  = Map.fold (fun rank' _ (a:IMJA) -> Map.union rank' a.Rank) rank c2s
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
           | Some i' when not (Type.subtype d i i') ->
               empty s
           | _ ->
               let rk = Store.nextReg x0
               let z0' = Set.add rk z0
               let trans, rank, owner, qfs, ss = mkMethodsAutomaton d g x rk i mths mu s
               let s1 = Map.add rk (i, Store.mkDefaultObj d i) s
               let s1', pi1 = Store.findWithWitness z0' s1 ss
               let q0 = newState ()
               let q0' = newState ()
               let q0q0' = {Start=q0; Label=MoveL (NoopL (Set.singleton rk, (ValM (VReg rk), s1))); End=q0'}
               let q1 = qfs.[s1']
               let q0'q1 = {Start=q0'; Label=PermL pi1; End=q1}
               let owner' = Map.add q0 P (Map.add q0' O owner)
               let rank'  = Map.add q0 s (Map.add q0' s1 rank)
               let trans' = q0q0' :: q0'q1 :: trans
               {
                 Final = List.map (fun s -> qfs.[s]) ss
                 InitR = Set.toList x0
                 InitS = q0
                 Owner = owner'
                 Rank = rank'
                 States = q0 :: List.map getSndState trans'
                 TransRel = trans'
               } 
       | Let (x, NewB (x',i,mths), c') ->
           let rk = Store.nextReg x0
           let z0' = Set.add rk z0
           let psi0 = Store.mkDefaultObj d i
           let r0 = Map.singleton rk (i, psi0)
           let g' = g @ [(x,Ty.Iface i)]
           let mu' = mu @ [ValM (VReg rk)]
           let s0' = Map.union s r0
           let ac' = fromCanon d g' c' mu' s0' 
           let a' = nu d ac' r0
           let trans, rank, owner, qfs, ss = mkMethodsAutomaton d g x' rk i mths mu s
           let ftrans, rest = List.partition (fun tr -> isFinalTrans a' tr) a'.TransRel
           let accTrans = ref (trans @ rest)
           let accOwner = ref (Map.union owner a'.Owner)
           let accRank = ref (Map.union rank a'.Rank)
           for tr in ftrans do
            match tr.Label with
            | MoveL (NoopL (x, (ValM (VReg r), s''))) when r = rk -> 
                let q = tr.Start
                let qf = tr.End
                let sj' = Store.trim s'' z0'
                let z = Map.domain sj'
                let q' = newState ()
                let q'' = newState ()
                do accOwner := Map.add q'' O (Map.add q' O !accOwner)
                do accRank := Map.add q'' (Map.restrict s'' z) (Map.add q' s'' !accRank)
                let qq' = {Start=q; Label=MoveL (NoopL (x, (ValM (VReg r), s''))); End=q'}
                let q'q'' = {Start=q'; Label=SetL z; End=q''}
                let sj, pi = Store.findWithWitness z0' sj' ss
                let q''qfsj = {Start=q''; Label=PermL pi; End=qfs.[sj]}
                accTrans := qq' :: q'q'' :: q''qfsj :: !accTrans
            | _ -> accTrans := tr :: !accTrans
           {
             Final = a'.Final @ (Seq.toList qfs.Values)
             InitR = a'.InitR
             InitS = a'.InitS
             Owner = !accOwner
             Rank = !accRank
             States = a'.InitS :: List.map getSndState !accTrans
             TransRel = !accTrans
           }
    // We deviate from the paper by additionally removing any unreachable structure.
    let pruned = prune automaton  
    pruned

