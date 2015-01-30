module IMJEquiv.InitialTests

open NUnit.Framework

[<Test>]
let ``empty context`` () =
  let g = []
  let result = Move.ofContext 3 g
  let expected = [pmove "*"]
  Assert.AreEqual (result, expected)

[<Test>]
let ``int context`` () =
  let g = ptyenv "x1: int, x2: int"
  let result = Move.ofContext 3 g
  let expected = [
    pmove "(0, 0)"
    pmove "(0, 1)"
    pmove "(1, 0)"
    pmove "(1, 1)"
  ]
  Assert.AreEqual (set result, set expected)

[<Test>]
let ``iface context`` () =
  let g = ptyenv "x1:I, x2:J"
  let result = Move.ofContext 3 g
  let expected = [pmove "(r3, r4)"]
  Assert.AreEqual (result, expected)

[<Test>]
let ``mixed context`` () =
  let g = ptyenv "x1: I, x2: int, x3: J"
  let result = Move.ofContext 3 g
  let expected = [
    pmove "(r3, 0, r4)"
    pmove "(r3, 1, r4)"
  ]
  Assert.AreEqual (result, expected)
