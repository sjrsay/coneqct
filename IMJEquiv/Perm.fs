namespace IMJEquiv
open IMJEquiv

type Perm<'a> when 'a : comparison = Map<'a,'a>

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Perm =
  
  let preApply (m: Map<'a,'b>) (p: Perm<'a>) : Map<'a,'b> =
    Map.fold (fun m' k v -> Map.add p.[k] v m') Map.empty m
         