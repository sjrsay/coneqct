module IMJEquiv.SchwoonTests

open NUnit.Framework

// Setup
do Schwoon.wInit ()
let sr = Schwoon.nulsr ()
let wPDS = Schwoon.wPDSCreate sr
let p = Schwoon.wIdentCreate("p")
let q = Schwoon.wIdentCreate("_q")
let r = Schwoon.wIdentCreate("__r__")
let s = Schwoon.wIdentCreate("__final_state__")
let a = Schwoon.wIdentCreate("a")
let z = Schwoon.wIdentCreate("z")
let _ = Schwoon.wPDSInsert (wPDS, p, z, p, z, a, System.IntPtr.Zero)
let _ = Schwoon.wPDSInsert (wPDS, p, a, p, a, a, System.IntPtr.Zero)
let _ = Schwoon.wPDSInsert (wPDS, p, a, q, a, 0, System.IntPtr.Zero)
let _ = Schwoon.wPDSInsert (wPDS, p, z, q, z, 0, System.IntPtr.Zero)
let _ = Schwoon.wPDSInsert (wPDS, q, a, q, 0, 0, System.IntPtr.Zero)
let _ = Schwoon.wPDSInsert (wPDS, q, z, r, z, 0, System.IntPtr.Zero)
let fa = Schwoon.wFACreate sr
let _ = Schwoon.wFAInsert (fa, r, z, s, System.IntPtr.Zero, System.IntPtr.Zero)
let fa' = Schwoon.wPrestar (wPDS, fa, (sbyte)0)


[<Test>]
let ``Stefan says yes`` () =
  let res = Schwoon.wFAFind (fa', p, z, s)
  Assert.AreEqual(res, System.IntPtr.Zero)

[<Test>]
let ``Stefan says no`` () =
  let res = Schwoon.wFAFind (fa', p, a, s)
  Assert.AreEqual(res, System.IntPtr.Zero)

[<TestFixtureTearDown>]
let clearUp () =
  do Schwoon.wPDSDelete wPDS
  do Schwoon.wFADelete fa
  do Schwoon.wFADelete fa'
  do Schwoon.wFinish ()
