module IMJEquiv.StoreTests

open NUnit.Framework

[<Test>]
let ``typed support test`` () =
  let d = pitbl "I = { f1: J, f2: int }, J = { f: void }"
  let s = pstore "r1 : I = { f1 = r2, f2 = 3 }, r2 : J = { f = * }"
  let expected = set [(1, "I"); (2, "J")]
  let actual = Store.tySupp d s
  Assert.AreEqual(expected, actual)