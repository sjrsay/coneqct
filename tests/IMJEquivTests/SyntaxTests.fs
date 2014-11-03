module IMJEquiv.SyntaxTests

open NUnit.Framework

[<Test>]
let ``nulls are alpha equiv`` () =
  let s = ptm "null"
  let t = ptm "null"
  let result = Term.alphaEq s t
  Assert.AreEqual(true, result)

[<Test>]
let ``distinct free vars are not alpha equiv`` () =
  let s = ptm "x"
  let t = ptm "y"
  let result = Term.alphaEq s t
  Assert.AreEqual (false, result)

[<Test>]
let ``sometimes lets are alpha equiv 1`` () =
  let s = ptm "let x = 3 in x"
  let t = ptm "let y = 3 in y"
  let result = Term.alphaEq s t
  Assert.AreEqual (true, result)

[<Test>]
let ``sometimes lets are alpha equiv 2`` () =
  let s = ptm "let x = 3 in z + (let y = 4 in y)"
  let t = ptm "let y = 3 in z + (let x = 4 in x)"
  let result = Term.alphaEq s t
  Assert.AreEqual (true, result)

[<Test>]
let ``sometimes lets are not alpha equiv`` () =
  let s = ptm "let x = 3 in (let y = 4 in x + y)"
  let t = ptm "let y = 3 in (let x = 4 in x + y)"
  let result = Term.alphaEq s t
  Assert.AreEqual (false, result)

[<Test>]
let ``sometimes news are alpha equiv 1`` () =
  let s = ptm @"new {z:I; m:\x y. x}"
  let t = ptm @"new {z:I; m:\u v. u}"
  let result = Term.alphaEq s t
  Assert.AreEqual (true, result)

[<Test>]
let ``sometimes news are not alpha equiv`` () =
  let s = ptm @"new {z:I; m:\x y. x}"
  let t = ptm @"new {z:I; m:\u v. v}"
  let result = Term.alphaEq s t
  Assert.AreEqual (false, result)

[<Test>]
let ``problematic let with null`` () =
  let s = ptm @"let x = null = y in x"
  let t = ptm @"let z = null = y in z"
  let result = Term.alphaEq s t
  Assert.AreEqual (true, result)

