// The definition of IMJ2 Automata (IMJ2A) and associated functions
// including the translation from pairs of IMJA.

namespace IMJEquiv

/// An IMJ2A state tracks the state of two
/// IMJA running in lock-step or, if one
/// becomes stuck, then the state of the remaining.
type IMJ2AState =
  | Sim of IMJAState * IMJAState  // Both automata are running in lock-step
  | Div1 of IMJAState             // Only the first automaton is running
  | Div2 of IMJAState             // Only the second automaton is running

  override x.ToString () =
    match x with
    | Sim (q1,q2) -> sprintf "(%O,%O)" q1 q2
    | Div1 q1     -> sprintf "(%O,_)" q1
    | Div2 q2     -> sprintf "(_,%O)" q2

/// The transition labels of an IMJ2 automaton.
/// There is some redundancy here (which kind of 
/// label of Move1 and Move2 is determined by the
/// kind of starting IMJ2AState on the transition),
/// but it makes the translation easier later.
type IMJ2ALabel =
  | Move12 of MoveLabel * MoveLabel    // A move in a Sim state
  | Move1 of MoveLabel                 // A move in a Div1 state
  | Move2 of MoveLabel                 // A move in a Div2 state
  | Set1Id of Set<RegId>               // A set restriction on the left in a Sim state
  | SetId2 of Set<RegId>               // A set restriction on the right in a Sim state
  | Set1 of Set<RegId>                 // A set restriction in a Div1 state
  | Set2 of Set<RegId>                 // A set restriction in a Div2 state
  | Perm1Id of Perm<RegId>             // A permutation on the left in a Sim state
  | PermId2 of Perm<RegId>             // A permutation on the right in a Sim state
  | Perm1 of Perm<RegId>               // A permutation in a Div1 state
  | Perm2 of Perm<RegId>               // A permutation in a Div2 state

/// A transition is just a triple
type IMJ2ATransition = IMJ2AState * IMJ2ALabel * IMJ2AState

/// The type of IMJ2 Automata
type IMJ2A =
  {
    States:  List<IMJ2AState>
    Owner:   IMJ2AState -> Player
    Rank:    Map<IMJ2AState,Store * Store>
    InitS:   IMJ2AState
    Trans:   List<IMJ2ATransition>
    Final:   List<IMJ2AState>
    NumRegs: Int
    InitC:   List<Move> * Store
  }

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module IMJ2A =

  /// Given an automaton a and a state q, returns all the transitions of a from q.
  let transFromState (a: IMJ2A) (q: IMJ2AState) : List<IMJ2ATransition> =
    List.filter (fun (q1,_,_) -> q = q1) a.Trans

  /// Given initial conditions (mu,s) and two IMJA a1 and a2
  /// the IMJ2 automaton which searches for a word contained in
  /// the symmetric difference of L(a1) and L(a2).
  let fromIMJA (a1: IMJA) (a2: IMJA) (mu: List<Move>, s: Store) : IMJ2A =
    // Follows the construction in the paper, see that for details.
    let a1OStates, a1PStates = 
      Map.partition (fun _ v -> v = O) a1.Owner
      |> fun (x,y) -> (Map.domainList x, Map.domainList y)
    let a2OStates, a2PStates = 
      Map.partition (fun _ v -> v = O) a2.Owner
      |> fun (x,y) -> (Map.domainList x, Map.domainList y)
    let statesByOwner (p: Player) (ps: List<IMJAState>) (os: List<IMJAState>) : List<IMJAState> =
      if p = P then ps else os
    let trans = ref []
    for t1 in a1.TransRel do
      match t1.Label with
      | MoveL tl1 ->
          let divTrans = (Div1 t1.Start, Move1 tl1, Div1 t1.End)
          trans := divTrans :: !trans
      | SetL x ->
          let divTrans = (Div1 t1.Start, Set1 x, Div1 t1.End)
          trans := divTrans :: !trans
          for q2 in statesByOwner a1.Owner.[t1.Start] a2PStates a2OStates do
            let idTrans = (Sim (t1.Start,q2), Set1Id x, Sim (t1.End,q2))
            trans := idTrans :: !trans
      | PermL pi ->
          let divTrans = (Div1 t1.Start, Perm1 pi, Div1 t1.End)
          trans := divTrans :: !trans
          for q2 in a2OStates do
            let idTrans = (Sim (t1.Start,q2), Perm1Id pi, Sim (t1.End,q2))
            trans := idTrans :: !trans
      for t2 in a2.TransRel do
        match t1.Label, t2.Label with
        | MoveL tl1, MoveL tl2 ->
            if a1.Owner.[t1.Start] = a2.Owner.[t2.Start] then
              let simTrans = (Sim (t1.Start,t2.Start), Move12 (tl1,tl2), Sim (t1.End,t2.End))
              trans := simTrans :: !trans
        | _, _ -> ()
    for t2 in a2.TransRel do
      match t2.Label with
      | MoveL tl2 ->
          let divTrans = (Div2 t2.Start, Move2 tl2, Div2 t2.End)
          trans := divTrans :: !trans
      | SetL x ->
          let divTrans = (Div2 t2.Start, Set2 x, Div2 t2.End)
          trans := divTrans :: !trans
          for q1 in statesByOwner a2.Owner.[t2.Start] a1PStates a1OStates do
            let idTrans = (Sim (q1,t2.Start), SetId2 x, Sim (q1,t2.End))
            trans := idTrans :: !trans
      | PermL pi ->
          let divTrans = (Div2 t2.Start, Perm2 pi, Div2 t2.End)
          trans := divTrans :: !trans
          for q1 in a1OStates do
            let idTrans = (Sim (q1,t2.Start), PermId2 pi, Sim (q1,t2.End))
            trans := idTrans :: !trans
    let owner (q:IMJ2AState) : Player =
      match q with
      | Sim (q', _) 
      | Div1 q'      -> a1.Owner.[q']
      | Div2 q'      -> a2.Owner.[q']
    let simO =
      List.productWith (fun x y -> Sim (x, y)) a1OStates a2OStates
    let simP =
      List.productWith (fun x y -> Sim (x, y)) a1OStates a2OStates
    let div1 = List.map (fun x -> Div1 x) a1.States
    let div2 = List.map (fun x -> Div2 x) a2.States
    let init = Sim (a1.InitS, a2.InitS)
    let final = div1 @ div2
    let states = simO @ simP @ final
    let rank =
      let rankPairState (m: Map<IMJ2AState,Store * Store>) (q: IMJ2AState) =
        match q with
        | Sim (q1, q2) -> Map.add q (a1.Rank.[q1], a2.Rank.[q2]) m
        | Div1 q1 -> Map.add q (a1.Rank.[q1], a1.Rank.[q1]) m
        | Div2 q2 -> Map.add q (a2.Rank.[q2], a2.Rank.[q2]) m
      List.fold rankPairState Map.empty states
    let numRegs1 = IMJA.numRegs a1
    let numRegs2 = IMJA.numRegs a2
    {
      States  = states
      Owner   = owner
      Rank    = rank
      InitS   = init
      Trans   = !trans
      Final   = final
      NumRegs = numRegs1 + numRegs2
      InitC   = (mu,s)
    }


