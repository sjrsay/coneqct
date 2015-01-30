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
    Control:    SpanState           
    Assignment: Array<ExtLet>   
  }

type FTLabel =
  | Eps
  | Push of (StackConst * Assn) * (StackConst * Assn)
  | Pop of (StackConst * Assn) * (StackConst * Assn)

type FTransition = FState * FTLabel * FState

type PDA = {
    States: List<FState>
    Trans: List<FTransition>
    Initial: FState
    Finals: List<FState>
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

  let setFlag (f: Flag) (e: ExtLet) : ExtLet =
    match e with
    | Empty -> Empty
    | Content (l,_) -> Content (l,f)

  let makeLocal (xs: Set<RegId>) (ass: Array<ExtLet>) : Array<ExtLet> =
    Array.mapi (fun i a -> if Set.contains i xs then setFlag Local a else a) ass

  let allLocal (xs: Set<RegId>) (ass: Array<ExtLet>) : Bool =
    let isLocal (e: ExtLet) : Bool =
      match e with
      | Empty         -> true  
      | Content (_,f) -> f = Local
    Set.forall (fun i -> isLocal ass.[i]) xs

  let globals (xs: Set<RegId>) : List<Map<RegId,Flag>> =
    let rec gs ys =
      match ys with
      | []     -> [Map.empty]
      | y::ys' ->
          [
            for m in gs ys' do
              for f in [Local; Global] do
                yield Map.add y f m
          ]
    gs (Set.toList xs)

  let successors (sz: Int) (q: FState) ((q1,tl,q2): Trans) : List<FTransition * FState> =
    let cut y rho = Array.foldi (fun m i l -> if Set.contains i y then Map.add i l m else m) Map.empty rho
    match tl with
    | TLabel.Noop x ->
        let flg = playerToFlag q1.Owner
        [
          for rho' in refresh sz x flg q.Assignment do
            let q' = { Control = q2; Assignment = rho' }
            let t' = (q, Eps, q')
            yield (t', q')
        ]
    | TLabel.Cut x ->
        let rho' = Array.mapi (fun i l -> if Set.contains i x then Empty else l) q.Assignment
        let q'   = { Control = q2; Assignment = rho' }
        [(q,Eps,q'),q']
    | TLabel.Eps -> 
        let q' = { q with Control = q2 }
        [(q,Eps,q'), q']
    | TLabel.Push (x, (p1,y1),(p2,y2)) ->
        let flg = playerToFlag q1.Owner
        let rhoy1 = cut y1 q.Assignment
        let rhoy2 = cut y2 q.Assignment
        [
          for rho' in refresh sz x flg q.Assignment do
            let rho'' = makeLocal (y1 + y2) rho'
            let q' = { Control = q2; Assignment = rho'' }
            yield ((q, Push ((p1,rhoy1),(p2,rhoy2)), q'), q')
        ]
    | TLabel.Pop (lfrs, (p1,y1), (p2,y2)) ->
        if not (allLocal (y1+y2) q.Assignment) then 
          []
        else
          let flg  = playerToFlag q1.Owner
          let exts = globals (y1+y2) 
          [
            for rho' in refresh sz lfrs Local q.Assignment do
              let rho'y1 = cut y1 rho'
              let rho'y2 = cut y2 rho'
              for ext in exts do
                let rho'y1g = Map.map (fun r l -> setFlag ext.[r] l) rho'y1
                let rho'y2g = Map.map (fun r l -> setFlag ext.[r] l) rho'y1
                let rho'g = Array.mapi (fun r l -> setFlag ext.[r] l) rho'
                let q' = { Control = q2; Assignment = rho'g }
                yield ((q, Pop ((p1,rho'y1g),(p2,rho'y2g)), q'), q')
          ]
        

  let fromFPDRA (a: FPDRA) : PDA =
    let sz = 3 * a.NumRegs

    let trans = ref []
    let states = HashSet ()

    let rec fix (fr: List<FState>) : Unit =
      if not (List.isEmpty fr) then
        let newFr = [
            for q in fr do
              for (q1,tl,q2) as t in a.Transitions do
                let succs = if q.Control = q1 then successors sz q t else []
                for (t',q') in succs do
                  do trans := t' :: !trans
                  let b = states.Add q'
                  if b then yield q'
          ]
        fix newFr

    let initRegMap = a.Initial.Span.Left // = Right, initially
    let initAssigned = Map.codomain initRegMap
    let letter = ref 0
    let assign (i:Int) =
      if Set.contains i initAssigned then
        do incr letter
        Content (!letter, Global)
      else
        Empty
    let rho0 = Array.init a.NumRegs assign
    let q0 = { Control = a.Initial; Assignment = rho0 }
    let _ = states.Add q0
    do fix [q0]

    let finals = [ for q in states do if List.contains q.Control a.Finals then yield q ] 
    {
      States  = List.ofSeq (states :> Seq<FState>)
      Trans   = !trans
      Initial = q0
      Finals  = finals
    }


