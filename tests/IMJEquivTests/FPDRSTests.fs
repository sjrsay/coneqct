module IMJEquiv.FPDRSTests

open NUnit.Framework

let q1q2 = Sim ({Val = 1}, {Val = 2})

let startState (q: State2) (o: Player) : SpanState =
  let span = {
      Left = Map.ofList [(2,1);(3,2)]
      Right = Map.ofList [(1,2);(4,4)]
    }
  let st = pstore "r1 : I = { f = r2 }, r2 : J = { g = 0 }, r4 : J = { g = 1 }"
  {
    State = q
    Span  = span
    Store = st
    Owner = o
  }


[<Test>]
let ``sim noop trans`` () =
  let q1q2' = Sim ({Val = 3}, {Val = 4})
  let x1  = set [1;4]
  let m1  = List.head (pmove "r1")
  let s1  = pstore "r1 : I = { f = r4 }, r4 : J = { g = 0 }, r2 : I = { f = r3 }, r3 : J = { g = 0 }"
  let tl1 = TransLabel.Noop (x1,(m1,s1))
  let x2  = set [2]
  let m2  = List.head (pmove "r2")
  let s2  = pstore "r2 : I = { f = r4 }, r4 : J = { g = 0 }"
  let tl2 = TransLabel.Noop (x2,(m2,s2))
  let t   = (q1q2, Move12 (tl1,tl2), q1q2')
  let qo  = startState q1q2 O
  let result = FPDRA.transFromTrans 8 qo t P
  let expSpan = {
      Left = Map.ofList [(2,1);(3,2);(1,3);(4,4)]
      Right = Map.ofList [(1,2);(4,4);(2,3)]
    }
  let expX = set [3]
  let expSt = pstore "r1 : I = { f = r2 }, r2 : J = { g = 0 }, r3 : I = { f = r4 }, r4 : J = { g = 0 }"
  let expq' = { State = q1q2'; Span = expSpan; Store = expSt; Owner = P }
  let expected = [
      (qo, TLabel.Noop expX, expq'), expq'
    ]
  Assert.AreEqual(set result, set expected)

[<Test>]
let ``sim diverges 1`` () =
  let q1q2' = Sim ({Val = 3}, {Val = 4})
  let x1  = set [1;4]
  let m1  = List.head (pmove "r1")
  let s1  = pstore "r1 : I = { f = r4 }, r4 : J = { g = 0 }, r2 : I = { f = r3 }, r3 : J = { g = 0 }"
  let tl1 = TransLabel.Noop (x1,(m1,s1))
  let x2  = set [2]
  let m2  = List.head (pmove "r2")
  let s2  = pstore "r2 : I = { f = r4 }, r4 : J = { g = 1 }"
  let tl2 = TransLabel.Noop (x2,(m2,s2))
  let t   = (q1q2, Move12 (tl1,tl2), q1q2')
  let qo  = startState q1q2 O
  let result = FPDRA.transFromTrans 8 qo t P
  let expSpanL = {
      Left = Map.ofList [(2,1);(3,2)]
      Right = Map.empty
    }
  let expSpanR = {
      Left = Map.empty
      Right = Map.ofList [(1,2);(4,4)]
    }
  let expStL = Map.restrict qo.Store (set [1;2])
  let expStR = Map.restrict qo.Store (set [2;4])
  let expq'L = { State = Div1 {Val = 1}; Span = expSpanL; Store = expStL; Owner = O }
  let expq'R = { State = Div2 {Val = 2}; Span = expSpanR; Store = expStR; Owner = O }
  let expected = [
      (qo, TLabel.Cut (set [1;2]), expq'L), expq'L
      (qo, TLabel.Cut (set [2;4]), expq'R), expq'R
    ]
  Assert.AreEqual(set result, set expected)

[<Test>]
let ``sim generates no transitions for P reasons`` () =
  let q1q2' = Sim ({Val = 3}, {Val = 4})
  let x1  = set [1;4]
  let m1  = List.head (pmove "r1")
  let s1  = pstore "r1 : I = { f = r4 }, r4 : J = { g = 0 }, r2 : I = { f = r3 }, r3 : J = { g = 1 }"
  let tl1 = TransLabel.Noop (x1,(m1,s1))
  let x2  = set [2]
  let m2  = List.head (pmove "r2")
  let s2  = pstore "r2 : I = { f = r4 }, r4 : J = { g = 0 }"
  let tl2 = TransLabel.Noop (x2,(m2,s2))
  let t   = (q1q2, Move12 (tl1,tl2), q1q2')
  let qo  = startState q1q2 P
  let result = FPDRA.transFromTrans 8 qo t O
  let expected = []
  Assert.AreEqual(set result, set expected)

[<Test>]
let ``joint noop trans even when O changes things`` () =
  let q1q2' = Sim ({Val = 3}, {Val = 4})
  let x1  = set [1;4]
  let m1  = List.head (pmove "r1")
  let s1  = pstore "r1 : I = { f = r4 }, r4 : J = { g = 0 }, r2 : I = { f = r3 }, r3 : J = { g = 1 }" // Here O changed r3
  let tl1 = TransLabel.Noop (x1,(m1,s1))
  let x2  = set [2]
  let m2  = List.head (pmove "r2")
  let s2  = pstore "r2 : I = { f = r4 }, r4 : J = { g = 0 }"
  let tl2 = TransLabel.Noop (x2,(m2,s2))
  let t   = (q1q2, Move12 (tl1,tl2), q1q2')
  let qo  = startState q1q2 O
  let result = FPDRA.transFromTrans 8 qo t P
  let expSpan = {
      Left = Map.ofList [(2,1);(3,2);(1,3);(4,4)]
      Right = Map.ofList [(1,2);(4,4);(2,3)]
    }
  let expX = set [3]
  let expSt = pstore "r1 : I = { f = r2 }, r2 : J = { g = 1 }, r3 : I = { f = r4 }, r4 : J = { g = 0 }"
  let expq' = { State = q1q2'; Span = expSpan; Store = expSt; Owner = P }
  let expected = [
      (qo, TLabel.Noop expX, expq'), expq'
    ]
  Assert.AreEqual(set result, set expected)

[<Test>]
let ``div noop transition`` () =
  let divq1 = Div1 {Val=1}
  let qo = startState divq1 O
  let qo' = { qo with Span = { qo.Span with Right = Map.empty } }
  let x1  = set [1;4]
  let m1  = List.head (pmove "r1")
  let s1  = pstore "r1 : I = { f = r4 }, r4 : J = { g = 0 }, r2 : I = { f = r3 }, r3 : J = { g = 1 }" // Here O changed r3
  let tl1 = TransLabel.Noop (x1,(m1,s1))
  let divq2 = Div1 {Val=2}
  let t   = (divq1, Move1 tl1, divq2)
  let result = FPDRA.transFromTrans 8 qo' t P
  let expSpan = {
      Left = Map.ofList [(2,1);(3,2);(1,3);(4,4)]
      Right = Map.empty
    }
  let expX = set [3;4]
  let expSt = pstore "r1 : I = { f = r2 }, r2 : J = { g = 1 }, r3 : I = { f = r4 }, r4 : J = { g = 0 }"
  let expq' = { State = divq2; Span = expSpan; Store = expSt; Owner = P }
  let expected = [
      (qo', TLabel.Noop expX, expq'), expq'
    ]
  Assert.AreEqual (result, expected)

[<Test>]
let ``joint push transition`` () =
  let q1q2' = Sim ({Val = 3}, {Val = 4})
  let x1  = set [1;4]
  let m1  = List.head (pmove "r1")
  let s1  = pstore "r1 : I = { f = r4 }, r4 : J = { g = 0 }, r2 : I = { f = r3 }, r3 : J = { g = 1 }" // Here O changed r3
  let tl1 = TransLabel.Push (x1,(m1,s1),{Val = 6}, set [2;3])
  let x2  = set [2]
  let m2  = List.head (pmove "r2")
  let s2  = pstore "r2 : I = { f = r4 }, r4 : J = { g = 0 }"
  let tl2 = TransLabel.Push (x2,(m2,s2),{Val = 5},set [1;4])
  let t   = (q1q2, Move12 (tl1,tl2), q1q2')
  let qo  = startState q1q2 O
  let result = FPDRA.transFromTrans 8 qo t P
  let expSpan = {
      Left = Map.ofList [(2,1);(3,2);(1,3);(4,4)]
      Right = Map.ofList [(1,2);(4,4);(2,3)]
    }
  let expX = set [3]
  let expSt = pstore "r1 : I = { f = r2 }, r2 : J = { g = 1 }, r3 : I = { f = r4 }, r4 : J = { g = 0 }"
  let expq' = { State = q1q2'; Span = expSpan; Store = expSt; Owner = P }
  let expected = [
      (qo, TLabel.Push (expX,({Val=6}:>_,set[1;2]),({Val=5}:>_,set[2;4])), expq'), expq'
    ]
  Assert.AreEqual(set result, set expected)

[<Test>]
let ``joint pop transition`` () =
  let q1q2' = Sim ({Val = 3}, {Val = 4})
  let x1  = set [1;4]
  let m1  = List.head (pmove "r1")
  let s1  = pstore "r1 : I = { f = r4 }, r4 : J = { g = 0 }, r2 : I = { f = r3 }, r3 : J = { g = 1 }" // Here O changed r3
  let tl1 = TransLabel.Pop (x1,(m1,s1),{Val = 6}, set[2;3;5], set[2;3])
  let x2  = set [2]
  let m2  = List.head (pmove "r2")
  let s2  = pstore "r2 : I = { f = r4 }, r4 : J = { g = 0 }"
  let tl2 = TransLabel.Pop (x2,(m2,s2),{Val = 5},set [1;4;5], set[1;4])
  let t   = (q1q2, Move12 (tl1,tl2), q1q2')
  let qo  = startState q1q2 O
  let result = FPDRA.transFromTrans 10 qo t P
  let expSpan1 = {
      Left = Map.ofList [(2,1);(3,2);(5,3);(1,5);(4,4)]
      Right = Map.ofList [(1,2);(4,4);(5,3);(2,5)]
    }
  let expSpan2 = {
      Left = Map.ofList [(2,1);(3,2);(5,3);(1,5);(4,4)]
      Right = Map.ofList [(1,2);(4,4);(5,1);(2,5)]
    }
  let expSpan3 = {
      Left = Map.ofList [(2,1);(3,2);(5,3);(1,6);(4,4)]
      Right = Map.ofList [(1,2);(4,4);(5,5);(2,6)]
    }
  let expX1 = set [3;5]
  let expX2 = set [3;5]
  let expX3 = set [3;5;6]
  let expSt1 = pstore "r1 : I = { f = r2 }, r2 : J = { g = 1 }, r5 : I = { f = r4 }, r4 : J = { g = 0 }"
  let expSt2 = pstore "r1 : I = { f = r2 }, r2 : J = { g = 1 }, r5 : I = { f = r4 }, r4 : J = { g = 0 }"
  let expSt3 = pstore "r1 : I = { f = r2 }, r2 : J = { g = 1 }, r6 : I = { f = r4 }, r4 : J = { g = 0 }"
  let expq'1 = { State = q1q2'; Span = expSpan1; Store = expSt1; Owner = P }
  let expq'2 = { State = q1q2'; Span = expSpan2; Store = expSt2; Owner = P }
  let expq'3 = { State = q1q2'; Span = expSpan3; Store = expSt3; Owner = P }
  let expected = [
      (qo, TLabel.Pop (expX1, ({Val=6}:>_,set[1;2;3]),({Val=5}:>_,set[2;4;3])), expq'1), expq'1
      (qo, TLabel.Pop (expX2, ({Val=6}:>_,set[1;2;3]),({Val=5}:>_,set[2;4;1])), expq'2), expq'2
      (qo, TLabel.Pop (expX3, ({Val=6}:>_,set[1;2;3]),({Val=5}:>_,set[2;4;5])), expq'3), expq'3
    ]
  let res = set result
  let exp = set expected
  Assert.AreEqual(set result, set expected)
