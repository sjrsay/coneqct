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

let specs = [
    "-o", ArgType.String (fun s -> outputFile := s), "Name of output dot file for automaton, default is \"auto.dot\"."
  ] 

let compiledSpecs = List.map (fun (sh, ty, desc) -> ArgInfo(sh, ty, desc)) specs

let usageText = "Please specify input file and command line options."

let _ = ArgParser.Parse(compiledSpecs, getInputFile, usageText)

let checkInitialConditions (d: ITbl) (g: TyEnv) (mu: List<Move>) (s: Store) =
  
  let assertInStore (r: RegId) (i: IntId) : Unit =
    match Map.tryFind r s with
    | None -> exitWith (sprintf "Malformed input: Register %d is not in the domain of the store." r)
    | Some (j,_) -> if i <> j then exitWith (sprintf "Malformed input: The type of register %d is inconsistent." r)

  let assertMoveType (x, ty: Ty) (m: Move) : Unit =
    match ty, m with
    | Ty.Void, Move.ValM Val.VStar   -> ()
    | Ty.Int, Move.ValM (Val.VNum _) -> ()
    | Ty.Iface i, Move.ValM (Val.VReg r) -> assertInStore r i
    | _, _ -> exitWith (sprintf "Malformed input: Move %A is not a valid initial move for (%A: %A)." m x ty)

  let assertStoreTyped : Unit =
    let assertFieldTyped (flds: Map<FldId, Val>) (f: FldId, ty: Ty) : Unit =
      match Map.tryFind f flds with
      | None -> exitWith (sprintf "Malformed input: Field %A is not assigned in the store." f)
      | Some v ->
          match v, ty with
          | Val.VNul, Ty.Iface _ -> ()
          | Val.VNum _, Ty.Int -> ()
          | Val.VReg r, Ty.Iface j -> assertInStore r j
          | Val.VStar, Ty.Void -> ()
          | _, _ -> exitWith (sprintf "Malformed input: Field %A assigned %A, but this is badly typed." f v)

    let assertFieldsOk (i: IntId) (flds: Map<FldId, Val>) : Unit =
      let fldSpec = ITbl.fields d i
      let fldDom = Map.domain flds
      Set.iter (fun f -> if List.forall (fun (g,_) -> f <> g) fldSpec then exitWith (sprintf "Malformed input: Field %A in initial store is not part of declared interface." f)) fldDom
      List.iter (assertFieldTyped flds) fldSpec

    Map.iter (fun _ (i, flds) -> assertFieldsOk i flds) s

  let relevantStore = Store.trim s (Automata.muSupp mu)
  let sDom = Map.domain s

  if sDom <> (Store.supp relevantStore) then exitWith (sprintf "Malformed input: Items in store unreachable from the initial move.")
  if List.length g > List.length mu then exitWith (sprintf "Malformed input: There are free variables not accounted for in the initial move.")
  if List.length g < List.length mu then exitWith (sprintf "Malformed input: There are components of the initial move not accounted for in the context.")
  List.iter2 assertMoveType g mu

  


[<EntryPoint>]
let main _ = 
    if !inputFile = "" then exitWith (sprintf "No input file specified.")
    let d, g, tm1, tm2 = 
      try Parsing.input !inputFile with
      | Parser.ParseError (s,l,c) -> exitWith (sprintf "Parse Error %d:%d: %s." l c s)
    let c1 = Canonical.canonise d g tm1
    let c2 = Canonical.canonise d g tm2
    let mus = Move.ofContext 1 g
    let inits = seq {
        for mu in mus do 
          for s in Store.fromMoves d g mu do
            yield (mu, s)
      }
    let autos = seq {
      for mu, s in inits do
        let a1 = Automata.fromCanon d g c1 mu s
        let a2 = Automata.fromCanon d g c2 mu s
        yield (a1, a2, mu, s)
    }
    let products = Seq.map (fun (a1,a2,mu,s) -> Product.fromAutomata (mu,s) a1 a2) autos
    let fpdras = Seq.map FPDRA.fromProduct products
    let pdas = Seq.map Explosion.fromFPDRA fpdras
    let forced = List.ofSeq pdas
    let pda = List.head forced
    printf "\nNum States = %d\n\n" pda.States.Length
//    let dot = Automata.toDot a
//    System.IO.File.WriteAllText(!outputFile, dot)
    0
