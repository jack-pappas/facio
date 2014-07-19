(*

Copyright 2014 Jack Pappas

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

namespace Facio.BuildTasks

open System.Reflection
open System.Threading


//
type internal ResolveHelper () =
    static let (|Version|) (version : System.Version) =
        Version (version.Major, version.Minor, version.Build, version.Revision)

    /// Indicates whether the event handler has been installed.
    /// Zero indicates the handler has not been installed; a non-zero value indicates it has.
    let mutable handlerInstalled = 0

    /// Delegate to the ResolveAssembly method.
    /// Cached so it can be added/removed from the event as needed.
    let handlerDelegate = System.ResolveEventHandler ResolveHelper.ResolveAssembly

    // Binding redirects for FSharp.Core can't be applied (easily, anyway) to MSBuild tasks,
    // meaning that our tasks will crash if run on a machine that doesn't have the exact version(s)
    // of FSharp.Core used by the facio tools.
    // This event handler fixes that by "manually" redirecting requests for older versions of
    // FSharp.Core to the newest available version on the machine.
    static member private ResolveAssembly _ (e : System.ResolveEventArgs) : Assembly =
        // Get an AssemblyName from the name specified in the event args.
        let assemblyName = AssemblyName (e.Name)
        
        // We only care about resolving FSharp.Core references; return null for anything else.
        if assemblyName.Name <> "FSharp.Core" then null else

        // Try to resolve older versions of FSharp.Core using newer versions.
        match assemblyName.Version with
        | Version (4, 0, 0, 0) ->
            // Try to resolve this to 4.3.1.0 first.
            try
                let fscoreName_4_3_1_0 = assemblyName.Clone () :?> AssemblyName
                fscoreName_4_3_1_0.Version <- System.Version (4, 3, 1, 0)
                Assembly.Load fscoreName_4_3_1_0
            with _ ->
                try
                    let fscoreName_4_3_0_0 = assemblyName.Clone () :?> AssemblyName
                    fscoreName_4_3_0_0.Version <- System.Version (4, 3, 0, 0)
                    Assembly.Load fscoreName_4_3_0_0
                with _ -> null

        | Version (4, 3, 0, 0) ->
            // Try to resolve this to 4.3.1.0.
            try
                let fscoreName_4_3_1_0 = assemblyName.Clone () :?> AssemblyName
                fscoreName_4_3_1_0.Version <- System.Version (4, 3, 1, 0)
                Assembly.Load fscoreName_4_3_1_0
            with _ -> null

        | _ ->
            // Don't know how to resolve this version so return null.
            null

    //
    member __.InstallHandler () =
        // Is the handler already installed? If so, there's nothing else to do.
        if Interlocked.Exchange (&handlerInstalled, 1) = 1 then () else

        System.AppDomain.CurrentDomain.add_AssemblyResolve handlerDelegate
