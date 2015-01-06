namespace IMJEquiv
open IMJEquiv


type Letter = Int

type Flag =
  | Local
  | Global

type ExtLet = 
  | Content of Letter * Flag
  | Empty

type Assn = Map<Int,ExtLet>

type FState = {
    Control: State           
    Registers: Array<ExtLet>   
    Store: Store
  }

type FTransition =
  | Eps of FState * FState
  | Push of FState * FState * Store * Assn
  | Pop of FState * FState * Store * Set<Int> * Set<Int>

type PDA = {
    States: List<FState>
    Trans: List<FTransition>
  }

type EIMJConfig = {
    State: State
    Owner: Player
    Assignment: Array<ExtLet>
    Stack: List<Store * Assn>
  }

module Explosion =

  let supp (rho: Array<ExtLet>) : Set<Letter> =
    Array.fold (fun acc el -> match el with Content (l,f) -> Set.add l acc | _ -> acc) Set.empty rho

  let allLocallyFresh (sz: Int) (rho: Array<ExtLet>) : List<Letter> =
    let sp = supp rho
    [for i in [1..sz] do if not (Set.contains i sp) then yield i]

  /// Given the size of the alphabet `sz` a set of integers to be excluded `exclude`
  /// and the length of the vector `n`, `allRefreshements` is a list of all possible 
  /// lists of the form `a1 ... an` in which each `ai` is a distinct  element of 
  /// `[1..sz]\exclude`.
  let allRefreshments (sz: Int) (exclude: Set<Int>) (n: Int) : List<List<Int>> =
    let rec build ex m =
      if n = 0 then
        [[]]
      else
        [
          for i in [1..sz] do 
            if not (Set.contains i ex) then 
              for xs in build (Set.add i ex) (n-1) do
                yield i::xs
        ]
    build exclude n

  let refresh (sz: Int) (xs: Set<RegId>) (f: Flag) (rho: Array<ExtLet>) : List<Array<ExtLet>> =
    let assignments = allRefreshments sz (supp rho) (Set.count xs)
    let mkNewArr (assn: List<Letter>) =
      let a = ref assn
      let f (i: Int) (el: ExtLet) =
        if Set.contains i xs then
          // Should be empty...
          match el with
          | Empty -> let hd = List.head !a in a := List.tail !a; Content (hd, f)
          | Content _ -> failwith "Refreshed register was expected to be empty."
        else
          el
      f
    [for ass in assignments do yield Array.mapi (mkNewArr ass) rho]

  let lookup (rho: Array<ExtLet>) (r: RegId) : Letter =
    match rho.[r] with
    | Empty -> failwith "Register not assigned."
    | Content (l,_) -> l

  let assignToVal (rho: Array<ExtLet>) (v: Val) : Val =
    match v with
    | VNum _ -> v
    | VStar  -> v
    | VNul   -> v
    | VReg r -> VReg (lookup rho r)

  let assignToMove (rho: Array<ExtLet>) (mu: Move) : Move =
    match mu with
    | ValM v -> ValM (assignToVal rho v)
    | Call (r, m, vs) -> Call (lookup rho r, m, List.map (assignToVal rho) vs)
    | Ret (r, m, v) -> Ret (lookup rho r, m, assignToVal rho v)

  let assignToStore (rho: Array<ExtLet>) (s: Store) : Store =
    let relabel (acc: Store) (k: RegId) (i: IntId, m: Map<FldId, Val>) : Store =
      let k' = lookup rho k
      let m' = Map.map (fun _ v -> assignToVal rho v) m
      Map.add k' (i, m') acc
    Map.fold relabel Map.empty s

  let playerToFlag (x: Player) : Flag =
    match x with
    | P -> Global
    | O -> Local

  let alternate (x: Player) : Player =
    match x with
    | P -> O
    | O -> P

  let successors (sz: Int) (conf: EIMJConfig) (t: Transition) : List<Move * Store * EIMJConfig> =
    match t with
    | LabelT (q1, tl, q2) ->
        let flg = playerToFlag conf.Owner 
        match tl with
        | Noop (x, (m, s)) ->
            [
              for rho' in refresh sz x flg conf.Assignment do
                let m' = assignToMove rho' m
                let s' = assignToStore rho' s
                let conf' = { 
                    conf with State = q2; Owner = alternate conf.Owner; Assignment = rho'
                  }
                yield (m', s', conf')
            ]

//  let fromProduct (sz: Int) (a: Automaton2) =
//    let alphabet = [1..sz]


