module IMJEquiv.CanonicalTests

open IMJEquiv.Canonical
open NUnit.Framework

[<Test>]
let ``hello returns 42`` () =
  let result = 20+22
  printfn "%i" result
  Assert.AreEqual(42,result)
