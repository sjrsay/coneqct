
open System
open System.IO
open System.Diagnostics
open System.Text.RegularExpressions
open System.Collections.Generic

let dir = "inputs"

let numTrials = 10

// Set the correct working directory
do System.Environment.CurrentDirectory <- __SOURCE_DIRECTORY__ + @"..\..\..\Release"

// Get test inputs
let inputFiles = Directory.GetFiles ("inputs","*.imj")

// Specify how to start coneqct on any given input file
let procSpec (inp: string) =
  let psi = new ProcessStartInfo() 
  do psi.FileName               <- "coneqct.exe"
  do psi.Arguments              <- inp
  do psi.UseShellExecute        <- false
  do psi.RedirectStandardOutput <- true
  do psi.CreateNoWindow         <- true
  psi

// Specify how to get the right part of the output
let getTime (output: string) : int =
  let m = Regex.Match (output, "Result: \w+ \((\d+)ms\)")
  // Uncomment the next line to see the individual times
  //printf "Match = %s\n" m.Groups.[1].Value
  Int32.Parse (m.Groups.[1].Value)

// Run coneqct on an input converting the output to an int
let run (inp: string) : int =
  let coneqct = Process.Start (procSpec inp)
  do coneqct.WaitForExit ()
  let output = coneqct.StandardOutput.ReadToEnd ()
  getTime output

let mean n xs = Seq.sum xs / n
let se (n: int) (times: int[]) (mean: int) =
  let square n = n * n
  let diffs = Array.map (fun t -> square (t - mean)) times
  let variance = (Array.sum diffs) / (n-1)
  let sd = Math.Sqrt ((float) variance)
  sd / (Math.Sqrt (float n))

// Run something n times and accumulate the result
let runManyTimes (n: int) (inputs: string[]) : unit =
  
  do printfn "Running %d trials..." n

  let times = Dictionary ()

  // Initialise the arrays
  for inp in inputs do
    times.[inp] <- Array.create n 0

  // Capture the times
  for i in [0..n-1] do
    for inp in inputs do
      times.[inp].[i] <- run inp 

  // Calculate the means
  let means = Dictionary ()
  for inp in inputs do 
    means.[inp] <- mean n times.[inp]

  // Calculate the standard errors
  let ses = Dictionary ()
  for inp in inputs do
    ses.[inp] <- se n times.[inp] means.[inp]

  // Print the means and standard errors
  for inp in inputs do
    printfn "%s: mean = %d, se = %f" inp means.[inp] ses.[inp]

runManyTimes numTrials inputFiles

