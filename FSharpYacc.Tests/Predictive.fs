(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpYacc.Tests.Predictive

open NUnit.Framework
open FsUnit

open FSharpYacc
open Predictive
open Ast


// TEST
(*
/// Grammar 3.8 from "Modern Compiler Implementation in ML"
let grammar_3_8 =
    /// Factor.
    let F =
        Set.empty
        |> Set.add [|
            Terminal "id"; |]
        |> Set.add [|
            Terminal "num"; |]
        |> Set.add [|
            Terminal "(";
            Nonterminal 'E';
            Terminal ")"; |]

    /// Term.
    let T =
        Set.empty
        |> Set.add [|
            Nonterminal 'T';
            Terminal "*";
            Nonterminal 'F'; |]
        |> Set.add [|
            Nonterminal 'T';
            Terminal "/";
            Nonterminal 'F'; |]
        |> Set.add [|
            Nonterminal 'F'; |]

    /// Expression.
    let E =
        Set.empty
        |> Set.add [|
            Nonterminal 'E';
            Terminal "+";
            Nonterminal 'T'; |]
        |> Set.add [|
            Nonterminal 'E';
            Terminal "-";
            Nonterminal 'T'; |]
        |> Set.add [|
            Nonterminal 'T'; |]

    // Create the grammar from the productions.
    {   Terminals =
            Set.empty
            |> Set.add "+"
            |> Set.add "-"
            |> Set.add "*"
            |> Set.add "/"
            |> Set.add "("
            |> Set.add ")"
            |> Set.add "id"
            |> Set.add "num";

        Nonterminals =
            Set.empty
            |> Set.add 'E'
            |> Set.add 'T'
            |> Set.add 'F';

        Productions =
            Map.empty
            |> Map.add 'E' E
            |> Map.add 'T' T
            |> Map.add 'F' F; }

let grammar_3_8_sets =
    GrammarAnalysis.ofGrammar grammar_3_8
*)

(*
//
let grammar_3_12 =
    let Z =
        Set.empty
        |> Set.add [|
            Terminal 'd'; |]
        |> Set.add [|
            Nonterminal 'X';
            Nonterminal 'Y';
            Nonterminal 'Z'; |]

    let Y =
        Set.empty
        |> Set.add [| |]    // Empty production
        |> Set.add [|
            Terminal 'c'; |]
   
    let X =
        Set.empty
        |> Set.add [|
            Nonterminal 'Y'; |]
        |> Set.add [|
            Terminal 'a'; |]

    {   Terminals =
            Set.empty
            |> Set.add 'a'
            |> Set.add 'c'
            |> Set.add 'd';
        Nonterminals =
            Set.empty
            |> Set.add 'X'
            |> Set.add 'Y'
            |> Set.add 'Z';
        Productions =
            Map.empty
            |> Map.add 'X' X
            |> Map.add 'Y' Y
            |> Map.add 'Z' Z; }

let grammar_3_12_analysis =
    GrammarAnalysis.ofGrammar grammar_3_12
*)

