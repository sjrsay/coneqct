module IMJEquiv.Serialise

  open RegSat

  let initState (n:Int) (q: SpanState) (i: State) =
    let ls = Map.codomain q.Span.Left
    let rs = Map.codomain q.Span.Right
    let regs = ls + rs
    let f i =
      if i = 0 then 
        Empty 
      elif Set.contains i regs then 
        Filled Local
      else
        Empty
    let arr = Array.init (n+1) f
    { Id=i; Flags=arr }

  let fpdra (p: FPDRA) : FPDRS * State * List<State> =

    let sNum = ref 0
    let sTbl = HashMap ()
    let state (q: SpanState) : State =
      match HashMap.tryFind q sTbl with
      | Some s -> s
      | None ->
          do incr sNum
          sTbl.[q] <- !sNum
          !sNum

    let newState () : RegSat.State =
      incr sNum; !sNum

    let tNum = ref 0
    let tTbl = HashMap ()
    let tag (q: IMJAState) : Int =
      match HashMap.tryFind q tTbl with
      | Some i -> i
      | None ->
          do incr tNum
          tTbl.[q] <- !tNum
          !tNum

    let rec serie q1 op xs q2 =
      match xs with
      | []  -> [{ Start=q1; Op=Eps; End=q2 }]
      | [e] -> [{ Start=q1; Op=op e; End=q2 }]
      | e::es ->
          let q1' = newState ()
          let es' = serie q1' op es q2
          { Start=q1; Op=op e; End=q1' } :: es'

    let trans : List<FPDRSTrans> = [
      for (q1,tl,q2) in p.Transitions do
        let q1' = state q1
        let q2' = state q2
        match tl with
        | TLabel.Cut xs -> 
            let erasees = Set.difference (set [1..p.NumRegs]) xs
            yield! serie q1' Erase (Set.toList erasees) q2'
        | TLabel.Noop xs ->
            let fre = if q1.Owner = P then GFresh else LFresh
            yield! serie q1' fre (Set.toList xs) q2'
        | TLabel.Push (xs, (c1,ys1), (c2,ys2)) ->
            let fre  = if q1.Owner = P then GFresh else LFresh
            let mid1 = newState ()
            let mid2 = newState ()
            let c1'  = tag c1
            let c2'  = tag c2
            let freTrans   = serie q1' fre (Set.toList xs) mid1
            let pushTrans1 = serie mid1 (fun i -> Push (c1',i)) (Set.toList ys1) mid2
            let pushTrans2 = serie mid2 (fun i -> Push (c2',i)) (Set.toList ys2) q2'
            yield! freTrans @ pushTrans1 @ pushTrans2
        | TLabel.Push1 (xs, (c1,ys1)) ->
            let fre  = if q1.Owner = P then GFresh else LFresh
            let mid1 = newState ()
            let c1'  = tag c1
            let freTrans   = serie q1' fre (Set.toList xs) mid1
            let pushTrans1 = serie mid1 (fun i -> Push (c1',i)) (Set.toList ys1) q2'
            yield! freTrans @ pushTrans1
        | TLabel.Pop (xs, (c1,ys1), (c2,ys2)) ->
            let fre  = if q1.Owner = P then GFresh else LFresh
            let mid1 = newState ()
            let mid2 = newState ()
            let c1'  = tag c1
            let c2'  = tag c2
            let freTrans   = serie q1' fre (Set.toList xs) mid1
            let popTrans1 = serie mid1 (fun i -> Pop (c2',i)) (List.rev (Set.toList ys2)) mid2
            let popTrans2 = serie mid2 (fun i -> Pop (c1',i)) (List.rev (Set.toList ys1)) q2'
            yield! freTrans @ popTrans1 @ popTrans2
        | TLabel.Pop1 (xs, (c1,ys1)) ->
            let fre  = if q1.Owner = P then GFresh else LFresh
            let mid1 = newState ()
            let c1'  = tag c1
            let freTrans   = serie q1' fre (Set.toList xs) mid1
            let popTrans2 = serie mid1 (fun i -> Pop (c1',i)) (List.rev (Set.toList ys1)) q2'
            yield! freTrans @ popTrans2
        | TLabel.PopFre c ->
            let c' = tag c
            yield { Start=q1'; Op=PopFresh c'; End=q2' }
        | TLabel.Eps -> yield { Start=q1'; Op=Eps; End=q2' }
    ]

    let fpdrs   = FPDRS.ofTransitions p.NumRegs trans
    let finals  = List.map state p.Finals
    let initial = state p.Initial
    (fpdrs, initial, finals)