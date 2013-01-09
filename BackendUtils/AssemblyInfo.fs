(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

/// Assembly-level attributes specific to this assembly.
module private AssemblyInfo

open System.Reflection
open System.Resources
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open System.Security
open System.Security.Permissions

[<assembly: AssemblyTitle("BackendUtils")>]
[<assembly: AssemblyDescription("A library containing utility modules used by the backends in 'fsharplex' and 'fsharpyacc'.")>]
[<assembly: NeutralResourcesLanguage("en-US")>]
[<assembly: Guid("8807f1f0-e13d-45fa-bf59-d1573a86a58a")>]

(* Dependency hints for Ngen *)
[<assembly: DependencyAttribute("FSharp.Core", LoadHint.Always)>]
[<assembly: DependencyAttribute("System", LoadHint.Always)>]

// Appease the F# compiler
do ()

