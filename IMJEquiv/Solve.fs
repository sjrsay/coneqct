namespace IMJEquiv

type Result = 
  | Equivalent
  | Inequivalent

  override x.ToString() =
    match x with
    | Equivalent -> "Contextually equivalent"
    | Inequivalent -> "Distinguished by some context"

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Result =
  
  let combine (r1: Result) (r2: Result) : Result =
    match r1, r2 with
    | Inequivalent, _            -> Inequivalent
    | _,            Inequivalent -> Inequivalent
    | _,            _            -> Equivalent

module Solve =

  let stateTbl = HashMap ()
  let letterTbl = HashMap ()
  let letters = HashSet ()

  let schwoon (p: PDA) : Result =

    let nul = System.IntPtr.Zero

    let qnum = ref 0
    let anum = ref 0

    let state (x: Int) = "q" + x.ToString ()
    let letter (x: Int) = "a" + x.ToString ()

    Schwoon.wInit()

    for q in p.States do
      match stateTbl.TryGetValue q with
      | true,  i -> ()
      | false, _ -> 
          incr qnum
          let qid = Schwoon.wIdentCreate (state !qnum)
          stateTbl.[q] <- qid

    for (_,tl,_) in p.Trans do
      match tl with
      | Eps         -> ()
      | Push (p,q) 
      | Pop  (p,q)  ->
          match letterTbl.TryGetValue ((p,q)) with
          | true, _ -> ()
          | false, _ ->
              incr anum
              let aid = Schwoon.wIdentCreate (letter !anum)
              letterTbl.[(p,q)] <- aid
              ignore (letters.Add aid)
  
    // Create the bottom of stack symbol
    let z = Schwoon.wIdentCreate "Z"
    ignore (letters.Add z)      

    // Create the final state of the FA
    let fin = Schwoon.wIdentCreate "__fin__"

    let sr = Schwoon.nulsr ()
    let wPDS = Schwoon.wPDSCreate sr
    let wFA = Schwoon.wFACreate sr
  
    for (q1,tl,q2) in p.Trans do
      let qid1 = stateTbl.[q1]
      let qid2 = stateTbl.[q2]
      match tl with
      | Eps -> 
          for a in letters do
            do ignore (Schwoon.wPDSInsert (wPDS, qid1, a, qid2, a, 0, nul))
      | Push (p,q) ->
          let aid = letterTbl.[(p,q)]
          for a in letters do
            do ignore (Schwoon.wPDSInsert (wPDS, qid1, a, qid2, a, aid, nul))
      | Pop (p,q) ->
          let aid = letterTbl.[(p,q)]
          do ignore (Schwoon.wPDSInsert (wPDS, qid1, aid, qid2, 0, 0, nul))

    for qf in p.Finals do
      let qfid = stateTbl.[qf]
      ignore (Schwoon.wFAInsert (wFA, qfid, z, fin, nul, nul))

    let wFA' = Schwoon.wPrestar (wPDS, wFA, (sbyte) 0)

    let q0 = stateTbl.[p.Initial]
    let res = Schwoon.wFAFind (wFA', q0, z, fin)

    do Schwoon.wPDSDelete wPDS
    do Schwoon.wFADelete wFA
    do Schwoon.wFADelete wFA'
    do Schwoon.wFinish ()

    if res = nul then Equivalent else Inequivalent
