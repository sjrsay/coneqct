module IMJEquiv.CanonicalTests

open NUnit.Framework

[<Test>]
let ``hello`` () =
  let tyEnv, tm = ptytm "x : int |- x "
  let result = Canonical.toTerm (Canonical.canonise tyEnv tm)
  let expected = ptm "x"
  printfn "%A" result
  Assert.AreEqual(expected,result)
