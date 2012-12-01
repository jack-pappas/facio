(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpLex.Program

open Graph
open Regex

//
module internal AssemblyInfo =
    open System.Reflection
    open System.Resources
    open System.Runtime.CompilerServices
    open System.Runtime.InteropServices
    open System.Security
    open System.Security.Permissions

    [<assembly: AssemblyTitle("FSharpLex")>]
    [<assembly: AssemblyDescription("A 'lex'-inspired lexical-analyzer-generator tool for F#.")>]
    [<assembly: NeutralResourcesLanguage("en-US")>]
    [<assembly: Guid("3e878e31-5c9a-456d-9ab8-a12e3fed1efe")>]

    (*  Makes internal modules, types, and functions visible
        to the test project so they can be unit-tested. *)
    #if DEBUG
    [<assembly: InternalsVisibleTo("FSharpLex.Tests")>]
    #endif

    // Appease the F# compiler
    do ()


open SpecializedCollections
open Regex

let ``(a + ba) + c`` =
    Regex.Or (
        Regex.Or (
            Regex.Character 'a',
            Regex.Concat (Regex.Character 'b', Regex.Character 'a')),
        Regex.Character 'c')

let derivativeClasses =
    let testUniverse =
        CharSet.empty
        |> CharSet.addRange 'a' 'z'
    Regex.DerivativeClasses (``(a + ba) + c``, testUniverse)

let ``ac + bc`` =
    Regex.Or (
        Regex.Concat (
            Regex.Character 'a',
            Regex.Character 'c'),
        Regex.Concat (
            Regex.Character 'b',
            Regex.Character 'c'))

// TEST : Compile a DFA for this regex.
let testDfa =
    Compile.rulePatternsToDfa [| ``ac + bc`` |]


printfn "Press any key to exit..."
System.Console.ReadKey ()
|> ignore

