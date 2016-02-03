(*

Copyright 2012-2013 Jack Pappas

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

/// Provides assembly-level attributes for the Reggie library.
module internal AssemblyInfo

open System.Reflection
open System.Resources
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open System.Security
open System.Security.Permissions

[<assembly: AssemblyTitle("Reggie")>]
[<assembly: AssemblyDescription("A library for working with regular expressions and their derivatives.")>]
[<assembly: NeutralResourcesLanguage("en-US")>]
[<assembly: Guid("bd62d0ce-26d3-4496-ade0-1b987d1ad67c")>]

(*  Makes internal modules, types, and functions visible
    to the test project so they can be unit-tested. *)
[<assembly: InternalsVisibleTo("Reggie.Tests")>]

(* Dependency hints for Ngen *)
[<assembly: DependencyAttribute("ExtCore", LoadHint.Always)>]
[<assembly: DependencyAttribute("FSharp.Core", LoadHint.Always)>]
[<assembly: DependencyAttribute("System", LoadHint.Always)>]

// Appease the F# compiler
do ()

