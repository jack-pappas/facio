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
open Ast

//let ``(a + ba) + c`` =
//    Regex.Or (
//        Regex.Or (
//            Regex.Character 'a',
//            Regex.Concat (
//                Regex.Character 'b',
//                Regex.Character 'a')),
//        Regex.Character 'c')
//
//let derivativeClasses =
//    let testUniverse =
//        CharSet.empty
//        |> CharSet.addRange 'a' 'z'
//    Regex.DerivativeClasses (``(a + ba) + c``, testUniverse)

let ``(a + ba) + c`` =
    LexerPattern.Or (
        LexerPattern.Or (
            LexerPattern.Character 'a',
            LexerPattern.Concat (
                LexerPattern.Character 'b',
                LexerPattern.Character 'a')),
        LexerPattern.Character 'c')

let ``ac + bc`` =
    LexerPattern.Or (
        LexerPattern.Concat (
            LexerPattern.Character 'a',
            LexerPattern.Character 'c'),
        LexerPattern.Concat (
            LexerPattern.Character 'b',
            LexerPattern.Character 'c'))

// TEST : Compile a DFA for this spec.
let testSpec = {
    Header = None;
    Footer = None;
    Macros = List.empty;
    Rules =
        Map.empty
        |> Map.add "TestRule" [
            { Pattern = ``ac + bc``; Action = ""; };
            { Pattern = ``(a + ba) + c``; Action = ""; };
            ];
    StartRule = "TestRule"; }

let testDfa =
    Compile.lexerSpec testSpec {
        Unicode = false; }


printfn "Press any key to exit..."
System.Console.ReadKey ()
|> ignore

