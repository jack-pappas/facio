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


//let wikipedia_grammar =
//    // NOTE : This grammar does not include the first rule
//    // which is the production of the augmented start symbol.
//    let E =
//        Set.empty
//        |> Set.add [|
//            Symbol.Nonterminal 'T'; |]
//        |> Set.add [|
//            Symbol.Terminal "(";
//            Symbol.Nonterminal 'E';
//            Symbol.Terminal ")"; |]
//
//    let T =
//        Set.empty
//        |> Set.add [|
//            Symbol.Terminal "n"; |]
//        |> Set.add [|
//            Symbol.Terminal "+";
//            Symbol.Nonterminal 'T'; |]
//        |> Set.add [|
//            Symbol.Nonterminal 'T';
//            Symbol.Terminal "+";
//            Symbol.Terminal "n"; |]
//
//    {   Terminals =
//            Set.empty
//            |> Set.add "n"
//            |> Set.add "+"
//            |> Set.add "("
//            |> Set.add ")";
//        Nonterminals =
//            Set.empty
//            |> Set.add 'E'
//            |> Set.add 'T';
//        Productions =
//            Map.empty
//            |> Map.add 'E' E
//            |> Map.add 'T' T;
//        StartSymbol = 'E'; }
//
//let foo =
//    Tables.Lr1.createTable wikipedia_grammar


let grammar_3_26 =
    // NOTE : This grammar does not include the first
    // rule of the grammar, which is the augmented start production.
    let S =
        Set.empty
        |> Set.add [|
            Symbol.Nonterminal 'V';
            Symbol.Terminal "=";
            Symbol.Nonterminal 'E'; |]
        |> Set.add [|
            Symbol.Nonterminal 'E'; |]

    let E =
        Set.empty
        |> Set.add [|
            Symbol.Nonterminal 'V'; |]

    let V =
        Set.empty
        |> Set.add [|
            Symbol.Terminal "x"; |]
        |> Set.add [|
            Symbol.Terminal "*";
            Symbol.Nonterminal 'E'; |]

    {   Terminals =
            Set.empty
            |> Set.add "="
            |> Set.add "x"
            |> Set.add "*";
        Nonterminals =
            Set.empty
            |> Set.add 'S'
            |> Set.add 'E'
            |> Set.add 'V';
        Productions =
            Map.empty
            |> Map.add 'S' S
            |> Map.add 'E' E
            |> Map.add 'V' V;
        StartSymbol = 'S'; }

let foo' =
    Tables.Lr1.createTable grammar_3_26


printfn "Press any key to exit..."
System.Console.ReadKey ()
|> ignore
