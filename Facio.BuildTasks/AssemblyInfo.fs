(*

Copyright 2012-2014 Jack Pappas

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

/// Assembly-level attributes specific to this assembly.
module private AssemblyInfo

open System.Reflection
open System.Resources
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open System.Security
open System.Security.Permissions

[<assembly: AssemblyTitle("Facio.BuildTasks")>]
[<assembly: AssemblyDescription("MSBuild tasks for Facio.")>]
[<assembly: NeutralResourcesLanguage("en-US")>]
[<assembly: Guid("1b289005-6d05-4709-ac72-f27e709bf2bc")>]

(* Dependency hints for Ngen *)
[<assembly: DependencyAttribute("FSharp.Core", LoadHint.Always)>]
[<assembly: DependencyAttribute("System", LoadHint.Always)>]

// Appease the F# compiler
do ()

