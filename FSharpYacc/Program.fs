(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpYacc.Program

open Tables
open Ast


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

    // Appease the F# compiler
    do ()


printfn "Press any key to exit..."
System.Console.ReadKey ()
|> ignore
