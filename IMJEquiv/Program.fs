module IMJEquiv.Program
open IMJEquiv

open Microsoft.FSharp.Text

let outputFile = ref "auto.dot"
let inputFile = ref ""

let exitWith (s:String) =
  printf "\n%s Exiting.\n" s; exit 1

let getOutputFile (s:String) : Unit =
  // Check that destination for output file exists
  let dir = System.IO.Path.GetDirectoryName s
  if System.IO.Directory.Exists dir then
    outputFile := s
  else
    exitWith (sprintf "Specified output location %s does not exist." dir)

let getInputFile (s:String) : Unit =
  // Check that file exists
  if System.IO.File.Exists s then
    inputFile := s
  else
    exitWith (sprintf "Specified input file %s does not exist." s)


// Command line options
let specs = [
    "-o", ArgType.String (fun s -> outputFile := s), "Name of output dot file for automaton, default is \"auto.dot\"."
  ] 
let compiledSpecs = List.map (fun (sh, ty, desc) -> ArgInfo(sh, ty, desc)) specs

// Command line usage string
let usageText = "Please specify input file and command line options."

// Parse command line options
let _ = ArgParser.Parse(compiledSpecs, getInputFile, usageText)


/// Given an interface table `d`, a type environment `g`, two canonical forms `c1` and `c2 such that 
/// `d g |- c1 : t` and `d g |- c2 : t` for some type `t` and an initial position `(mu, s)` consistent
/// with the context `d g`, `solveFromInitPos d g c1 c2 mu s` is `Equivalent` just if `c1` and `c2`
/// are contextually equivalent in `d g` and is `Inequivalent` otherwise.
let solveFromInitPos (d: ITbl) (g: TyEnv) (c1: Canon) (c2: Canon) (mu: List<Move>) (s: Store) : Result =

  do printf "Processing initial position (%s, %A):\n" (Move.listToString mu) s
  
  let a1    = Automaton.fromCanon d g c1 mu s
  do printf "\tIMJA 1: %d states, %d transitions.\n" a1.States.Length a1.TransRel.Length

  let a2    = Automaton.fromCanon d g c2 mu s
  do printf "\tIMJA 2: %d states, %d transitions.\n" a2.States.Length a2.TransRel.Length

  let imj2  = Product.fromAutomata (mu, s) a1 a2
  do printf "\tIMJ2A: %d states, %d transitions, %d registers.\n" imj2.States.Length imj2.Trans.Length imj2.NumRegs

  let fpdra = FPDRA.fromProduct imj2
  do printf "\tFPDRA: %d states, %d transitions.\n" fpdra.States.Length fpdra.Transitions.Length

  let pda   = Explosion.fromFPDRA fpdra
  do printf "\tPDA: %d states, %d transition.\n" pda.States.Length pda.Trans.Length
  
  let result = Solve.schwoon pda
  do printf "\tResult: %A\n\n" result

  result


/// The entry point to the program is `main`.  Assumes that all option handling has already been done.
[<EntryPoint>]
let main _ = 

    printf "\nContextual Equivalence Checker for Interface Middleweight Java\n\n"

    if !inputFile = "" then exitWith (sprintf "No input file specified.")
    let d, g, tm1, tm2 = 
      try Parsing.input !inputFile with
      | Parser.ParseError (s,l,c) -> exitWith (sprintf "Parse Error %d:%d: %s." l c s)
      | Lexer.LexerError  (_,l,c) -> exitWith (sprintf "Parse Error %d:%d: unknown symbol." l c)
      | _                         -> exitWith (sprintf "Parse Error: input is malformed.")
    let c1 = Canonical.canonise d g tm1
    let c2 = Canonical.canonise d g tm2
    let mus = Move.ofContext 1 g
    let inits = seq {
        for mu in mus do 
          for s in Store.fromMoves d g mu do
            yield (mu, s)
      }
    let res = Seq.fold (fun r (mu, s) -> Result.combine r (solveFromInitPos d g c1 c2 mu s)) Equivalent inits
    printf "Result: %A\n" res
    0
