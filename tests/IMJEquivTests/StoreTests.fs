module IMJEquiv.StoreTests

open NUnit.Framework

[<Test>]
let ``typed support test`` () =
  let d = pitbl "I = { f1: J, f2: int }, J = { f: void }"
  let s = pstore "r1 : I = { f1 = r2, f2 = 3 }, r2 : J = { f = * }"
  let expected = set [(1, "I"); (2, "J")]
  let actual = Store.tySupp d s
  Assert.AreEqual(expected, actual)

[<Test>]
let ``generate stores with numbers`` () =
  let d = pitbl "I = { f: int }, J = { g: void }"
  let s = pstore "r1 : I = { f = 3 }"
  let z = set [(3, "I"); (4, "I"); (5, "J")]
  do Val.maxint <- 2
  let actual = Store.stores d (Store.tySupp d s) z
  let expected = [
      pstore "r3 : I = { f = 0 }, r4 : I = { f = 0 }, r5 : J = { g = * }"
      pstore "r3 : I = { f = 0 }, r4 : I = { f = 1 }, r5 : J = { g = * }"
      pstore "r3 : I = { f = 0 }, r4 : I = { f = 2 }, r5 : J = { g = * }"
      pstore "r3 : I = { f = 1 }, r4 : I = { f = 0 }, r5 : J = { g = * }"
      pstore "r3 : I = { f = 1 }, r4 : I = { f = 1 }, r5 : J = { g = * }"
      pstore "r3 : I = { f = 1 }, r4 : I = { f = 2 }, r5 : J = { g = * }"
      pstore "r3 : I = { f = 2 }, r4 : I = { f = 0 }, r5 : J = { g = * }"
      pstore "r3 : I = { f = 2 }, r4 : I = { f = 1 }, r5 : J = { g = * }"
      pstore "r3 : I = { f = 2 }, r4 : I = { f = 2 }, r5 : J = { g = * }"
    ]
  Assert.AreEqual(set expected, set actual)

[<Test>]
let ``generate stores with registers`` () =
  let d = pitbl "I = { f: J }, J = { g: void }"
  let s = pstore "r1 : I = { f = r4 }, r2 : I = { f = r4 }, r3 : J = { g = * }, r4 : J = { g = * }"
  let z = set [(1, "I"); (2, "I"); (3, "J")]
  do Val.maxint <- 2
  let actual = Store.stores d (Store.tySupp d s) z
  let expected = [
      pstore "r1 : I = { f = r3 }, r2 : I = { f = r3 }, r3 : J = { g = * }"
      pstore "r1 : I = { f = r3 }, r2 : I = { f = r4 }, r3 : J = { g = * }, r4 : J = { g = * }"
      pstore "r1 : I = { f = r3 }, r2 : I = { f = r5 }, r3 : J = { g = * }, r5 : J = { g = * }"
      pstore "r1 : I = { f = r3 }, r2 : I = { f = null }, r3 : J = { g = * }"
      pstore "r1 : I = { f = r4 }, r2 : I = { f = r3 }, r3 : J = { g = * }, r4 : J = { g = * }"
      pstore "r1 : I = { f = r4 }, r2 : I = { f = r4 }, r3 : J = { g = * }, r4 : J = { g = * }"
      pstore "r1 : I = { f = r4 }, r2 : I = { f = r5 }, r3 : J = { g = * }, r4 : J = { g = * }, r5 : J = { g = * }"
      pstore "r1 : I = { f = r4 }, r2 : I = { f = null }, r3 : J = { g = * }, r4 : J = { g = * }"
      pstore "r1 : I = { f = r5 }, r2 : I = { f = r3 }, r3 : J = { g = * }, r5 : J = { g = * }"
      pstore "r1 : I = { f = r5 }, r2 : I = { f = r4 }, r3 : J = { g = * }, r4 : J = { g = * }, r5 : J = { g = * }"
      pstore "r1 : I = { f = r5 }, r2 : I = { f = r5 }, r3 : J = { g = * }, r5 : J = { g = * }"
      pstore "r1 : I = { f = r5 }, r2 : I = { f = r6 }, r3 : J = { g = * }, r5 : J = { g = * }, r6 : J = { g = * }"
      pstore "r1 : I = { f = r5 }, r2 : I = { f = null }, r3 : J = { g = * }, r5 : J = { g = * }"
      pstore "r1 : I = { f = null }, r2 : I = { f = r3 }, r3 : J = { g = * }"
      pstore "r1 : I = { f = null }, r2 : I = { f = r4 }, r3 : J = { g = * }, r4 : J = { g = * }"
      pstore "r1 : I = { f = null }, r2 : I = { f = r5 }, r3 : J = { g = * }, r5 : J = { g = * }"
      pstore "r1 : I = { f = null }, r2 : I = { f = null }, r3 : J = { g = * }"
    ]
  Assert.AreEqual(set expected, set actual)