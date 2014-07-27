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

/// Provides assembly-level attributes common to all projects
/// in the 'fsharp-tools' repository.
module internal CommonAssemblyInfo

open System.Reflection
open System.Runtime.CompilerServices
open System.Runtime.InteropServices

/// <summary>A subset of the conditional compilation symbols
/// specified when this assembly was compiled.</summary>
/// <remarks>Used for diagnostics purposes, e.g., to mark traced
/// and debug builds.</remarks>
let [<Literal>] private assemblyConfig =
    #if DEBUG
    #if TRACE
    "DEBUG;TRACE"
    #else
    "DEBUG"
    #endif
    #else
    #if TRACE
    "TRACE"
    #else
    ""
    #endif
    #endif

// General Information about an assembly is controlled through the following
// set of attributes. Change these attribute values to modify the information
// associated with an assembly.
[<assembly: AssemblyConfiguration(assemblyConfig)>]
[<assembly: AssemblyCopyright("Copyright � Jack Pappas 2012-2014")>]
//[<assembly: AssemblyTrademark("")>]
//[<assembly: AssemblyCulture("")>]

// Setting ComVisible to false makes the types in this assembly not visible
// to COM components.  If you need to access a type in this assembly from
// COM, set the ComVisible attribute to true on that type.
[<assembly: ComVisible(false)>]

// Version information
[<assembly: AssemblyVersion("0.8.8")>]
[<assembly: AssemblyFileVersion("0.8.8")>]
[<assembly: AssemblyInformationalVersion("0.8.8")>]

// Only allow types derived from System.Exception to be thrown --
// any other types should be automatically wrapped.
[<assembly: RuntimeCompatibility(WrapNonExceptionThrows = true)>]


(*  F# considers modules which only contain attributes to be empty;
    so, we appease the compiler by adding an empty function. *)
do ()
