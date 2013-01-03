(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

namespace FSharpYacc

/// Assembly-level attributes specific to this assembly.
module private AssemblyInfo =
    open System.Reflection
    open System.Resources
    open System.Runtime.CompilerServices
    open System.Runtime.InteropServices
    open System.Security
    open System.Security.Permissions

    [<assembly: AssemblyTitle("FSharpYacc")>]
    [<assembly: AssemblyDescription("A 'yacc'-inspired parser-generator tool for F#.")>]
    [<assembly: NeutralResourcesLanguage("en-US")>]
    [<assembly: Guid("fc309105-ce95-46d1-8cb4-568fc6bea85c")>]

    (*  Makes internal modules, types, and functions visible
        to the test project so they can be unit-tested. *)
    #if DEBUG
    [<assembly: InternalsVisibleTo("FSharpYacc.Tests")>]
    #endif

    (* Dependency hints for Ngen *)
    [<assembly: DependencyAttribute("FSharp.Core", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System.ComponentModel.Composition", LoadHint.Always)>]

    // Appease the F# compiler
    do ()


//
[<RequireQualifiedAccess>]
module Program =
    /// Invokes FSharpYacc with the specified options.
    [<CompiledName("Invoke")>]
    let invoke (options : CompilationOptions) : int =
        (* TODO :   Validate the compilation options before proceeding further. *)
        //

        // TEST : Test compilation and code generation using the test specification.
        let exitCode =
            match Compiler.compile (FSharpYacc.TestSpec.``fslex parser spec``, options) with
            | Choice1Of2 result ->
                // TODO : Pass the result to the selected backend.

                // BREAKPOINT
                let efowei = "weofkwokfwe".Length + 1

                0   // Success
            | Choice2Of2 errorMessages ->
                // Write the error messages to the console.
                // TODO : Write the error messages to NLog (or similar) instead, for flexibility.
                errorMessages
                |> List.iter (printfn "Error: %s")

                1   // Error

        // TEMP : Don't exit until pressing a key, so we can read any messages printed to the console.
        // This MUST be removed before FSharpYacc can be called from MSBuild, VS, etc.
        printfn ""
        printfn "Press any key to exit..."
        System.Console.ReadKey ()
        |> ignore

        // Return the exit code.
        exitCode

    /// The entry point for the application.
    [<EntryPoint; CompiledName("Main")>]
    let main (options : string[]) =
        (* TODO :   Parse command-line options and use the values to
                    create an instance of the CompilationOptions record,
                    then call the 'invoke' function with it. *)
        
        // TEST : Just use an empty CompilationOptions record for now.
        invoke {
            InputFile = ""; }
        

        
