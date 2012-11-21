(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpYacc.Tests.Tables

open NUnit.Framework
open FsUnit

open FSharpYacc
open Predictive
open Tables
open Ast


let grammar_3_20 =
    // NOTE : This grammar does not include the first rule,
    // which is the production of the augmented start symbol.
    let S =
        Set.empty
        |> Set.add [|
            Terminal "(";
            Nonterminal 'L';
            Terminal ")"; |]
        |> Set.add [|
            Terminal "x"; |]

    let L =
        Set.empty
        |> Set.add [|
            Nonterminal 'S'; |]
        |> Set.add [|
            Nonterminal 'L';
            Terminal ",";
            Nonterminal 'S'; |]

    {   Terminals =
            Set.empty
            |> Set.add "("
            |> Set.add ")"
            |> Set.add "x"
            |> Set.add ",";
        Nonterminals =
            Set.empty
            |> Set.add 'L'
            |> Set.add 'S';
        Productions =
            Map.empty
            |> Map.add 'L' L
            |> Map.add 'S' S;
        StartSymbol = 'S'; }
        
// TEST
let ``LR(0) table for Grammar 3.20`` =
    Tables.Lr0.createTable grammar_3_20


let grammar_3_23 =
    // NOTE : This grammar does not include the first rule,
    // which is the production of the augmented start symbol.
    let E =
        Set.empty
        |> Set.add [|
            Nonterminal 'T';
            Terminal "+";
            Nonterminal 'E'; |]
        |> Set.add [|
            Nonterminal 'T'; |]

    let T =
        Set.empty
        |> Set.add [|
            Terminal "x"; |]

    {   Terminals =
            Set.empty
            |> Set.add "x"
            |> Set.add "+";
        Nonterminals =
            Set.empty
            |> Set.add 'E'
            |> Set.add 'T';
        Productions =
            Map.empty
            |> Map.add 'E' E
            |> Map.add 'T' T;
        StartSymbol = 'E'; }

let ``LR(0) table for Grammar 3.23`` =
    Tables.Lr0.createTable grammar_3_23

let ``SLR table for Grammar 3.23`` =
    Tables.Slr.createTable grammar_3_23

