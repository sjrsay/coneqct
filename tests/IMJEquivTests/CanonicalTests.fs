module IMJEquiv.CanonicalTests

open NUnit.Framework

(*
  To test that canonical forms are created correctly, we create a typed term `G |- t`,
  canonise it to obtain `c` then convert `c` back to a term `t'` and check `t = t'`
  up to renaming of bound variables.
*)

[<Test>]
let ``variables are already canonical`` () =
  let tyEnv, tm = ptytm "x : int |- x "
  let result = Canonical.toTerm (Canonical.canonise tyEnv tm)
  let expected = ptm "x"
  AssertAlphaEqual(expected, result)

[<Test>]
let ``null is already canonical`` () =
  let tyEnv, tm = ptytm "|- null"
  let result = Canonical.toTerm (Canonical.canonise tyEnv tm)
  let expected = ptm "null"
  AssertAlphaEqual(expected, result)

[<Test>]
let ``ints are put in a let`` () =
  let tyEnv, tm = ptytm "|- 3"
  let result = Canonical.toTerm (Canonical.canonise tyEnv tm)
  let expected = ptm "let x = 3 in x"     
  AssertAlphaEqual(expected, result)

[<Test>]
let ``skip is put in a let`` () =
  let tyEnv, tm = ptytm "|- skip"
  let result = Canonical.toTerm (Canonical.canonise tyEnv tm)
  let expected = ptm "let x = skip in x"
  AssertAlphaEqual (expected, result)

[<Test>]
let ``complex additions require lemma 34`` () =
  let tyEnv, tm = ptytm "|- x + (let y = 3 in y)"
  let result = Canonical.toTerm (Canonical.canonise tyEnv tm)
  let expected = ptm "let z1 = 3 in let z2 = x + z1 in z2"
  AssertAlphaEqual (expected, result)

[<Test>]
let ``canonical form of null equals x`` () =
  let tyEnv, tm = ptytm "x:I |- null = x"
  let result = Canonical.toTerm (Canonical.canonise tyEnv tm)
  let expected = ptm "let y = null in let z = (null = x) in z"
  AssertAlphaEqual (expected, result)

