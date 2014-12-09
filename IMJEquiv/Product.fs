namespace IMJEquiv

type State2 =
  | Sim of State * State
  | Div1 of State
  | Div2 of State

type TLabel2 =
  | Move12 of TransLabel * TransLabel
  | Move1 of TransLabel
  | Move2 of TransLabel
  | Set1Id of Set<RegId>
  | SetId2 of Set<RegId>
  | Set1 of Set<RegId>
  | Set2 of Set<RegId>
  | Perm1Id of Perm<RegId>
  | PermId2 of Perm<RegId>
  | Perm1 of Perm<RegId>
  | Perm2 of Perm<RegId>

type Transition2 = State2 * TLabel2 * State2

type Automaton2 =
  {
    States: List<State2>
    Owner: State2 -> Player
    InitS: State2
    Trans: List<Transition2>
    Final: List<State2>
  }

module Product =

  let fromAutomata (a1: Automaton) (a2: Automaton) : Automaton2 =
    let a1OStates, a1PStates = 
      Map.partition (fun _ v -> v = O) a1.Owner
      |> fun (x,y) -> (Map.domainList x, Map.domainList y)
    let a2OStates, a2PStates = 
      Map.partition (fun _ v -> v = O) a2.Owner
      |> fun (x,y) -> (Map.domainList x, Map.domainList y)
    let statesByOwner (p: Player) (ps: List<State>) (os: List<State>) : List<State> =
      if p = P then ps else os
    let trans = ref []
    for t1 in a1.TransRel do
      match t1 with
      | LabelT (q1, tl1, q1') ->
          let divTrans = (Div1 q1, Move1 tl1, Div1 q1')
          trans := divTrans :: !trans
      | SetT (q1, x, q1') ->
          let divTrans = (Div1 q1, Set1 x, Div1 q1')
          trans := divTrans :: !trans
          for q2 in statesByOwner a1.Owner.[q1] a2PStates a2OStates do
            let idTrans = (Sim (q1,q2), Set1Id x, Sim (q1',q2))
            trans := idTrans :: !trans
      | PermT (q1, pi, q1') ->
          let divTrans = (Div1 q1, Perm1 pi, Div1 q1')
          trans := divTrans :: !trans
          for q2 in a2OStates do
            let idTrans = (Sim (q1,q2), Perm1Id pi, Sim (q1',q2))
            trans := idTrans :: !trans
      for t2 in a2.TransRel do
        match t1, t2 with
        | LabelT (q1,tl1,q1'), LabelT (q2,tl2,q2') ->
            if a1.Owner.[q1] = a2.Owner.[q2] then
              let simTrans = (Sim (q1,q2), Move12 (tl1,tl2), Sim (q1',q2'))
              trans := simTrans :: !trans
        | _, _ -> ()
    for t2 in a2.TransRel do
      match t2 with
      | LabelT (q2, tl2, q2') ->
          let divTrans = (Div2 q2, Move2 tl2, Div2 q2')
          trans := divTrans :: !trans
      | SetT (q2, x, q2') ->
          let divTrans = (Div2 q2, Set2 x, Div2 q2')
          trans := divTrans :: !trans
          for q1 in statesByOwner a2.Owner.[q2] a1PStates a1OStates do
            let idTrans = (Sim (q1,q2), SetId2 x, Sim (q1,q2'))
            trans := idTrans :: !trans
      | PermT (q2, pi, q2') ->
          let divTrans = (Div2 q2, Perm2 pi, Div2 q2')
          trans := divTrans :: !trans
          for q1 in a1OStates do
            let idTrans = (Sim (q1,q2), PermId2 pi, Sim (q1,q2'))
            trans := idTrans :: !trans
    let owner (q:State2) : Player =
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
    {
      States = simO @ simP @ final
      Owner  = owner
      InitS  = init
      Trans  = !trans
      Final  = final
    }

