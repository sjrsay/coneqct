#r @"packages/FAKE/tools/FakeLib.dll"
open Fake
open System

// Constants

let buildDir = "./bin/"
let testAssemblies = "./bin/*Tests.dll"
//let testAssemblies = "./tests/**/bin/Debug/*Tests.dll"
//let testBinDirs = "./tests/**/bin/"
let solutionFile = "./IMJEquiv.sln"

// Targets

Target "Restore" RestorePackages

Target "Clean" (fun _ ->
  CleanDir buildDir
)

Target "Build" (fun _ ->
  !! solutionFile
  |> MSBuildRelease buildDir "Rebuild" 
  |> ignore
)

Target "RunTests" (fun _ ->
  !! testAssemblies
  |> NUnit (fun p ->
      { p with
          DisableShadowCopy = true
          TimeOut = TimeSpan.FromMinutes 20.
          OutputFile = "TestResults.xml" 
          Framework = "net-4.5"
      })
)

// Dependencies

"Restore"
  ==> "Build"
  ==> "RunTests"

// Start build

RunTargetOrDefault "Build"
