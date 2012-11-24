(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

/// Test grammars.
module FSharpYacc.Tests.Grammars

open FSharpYacc
open Ast


/// Grammar 3.8 from "Modern Compiler Implementation in ML".
let grammar_3_8 =
    /// Factor.
    let F =
        Set.empty
        |> Set.add [|
            Symbol.Terminal "id"; |]
        |> Set.add [|
            Symbol.Terminal "num"; |]
        |> Set.add [|
            Symbol.Terminal "(";
            Symbol.Nonterminal 'E';
            Symbol.Terminal ")"; |]

    /// Term.
    let T =
        Set.empty
        |> Set.add [|
            Symbol.Nonterminal 'T';
            Symbol.Terminal "*";
            Symbol.Nonterminal 'F'; |]
        |> Set.add [|
            Symbol.Nonterminal 'T';
            Symbol.Terminal "/";
            Symbol.Nonterminal 'F'; |]
        |> Set.add [|
            Symbol.Nonterminal 'F'; |]

    /// Expression.
    let E =
        Set.empty
        |> Set.add [|
            Symbol.Nonterminal 'E';
            Symbol.Terminal "+";
            Symbol.Nonterminal 'T'; |]
        |> Set.add [|
            Symbol.Nonterminal 'E';
            Symbol.Terminal "-";
            Symbol.Nonterminal 'T'; |]
        |> Set.add [|
            Symbol.Nonterminal 'T'; |]

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
            |> Map.add 'F' F;
        // TODO : Make sure this start symbol is correct.
        StartSymbol = 'F'; }

/// Grammar 3.12 from "Modern Compiler Implementation in ML".
let grammar_3_12 =
    let Z =
        Set.empty
        |> Set.add [|
            Symbol.Terminal 'd'; |]
        |> Set.add [|
            Symbol.Nonterminal 'X';
            Symbol.Nonterminal 'Y';
            Symbol.Nonterminal 'Z'; |]

    let Y =
        Set.empty
        |> Set.add [| |]    // Empty production
        |> Set.add [|
            Symbol.Terminal 'c'; |]
   
    let X =
        Set.empty
        |> Set.add [|
            Symbol.Nonterminal 'Y'; |]
        |> Set.add [|
            Symbol.Terminal 'a'; |]

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
            |> Map.add 'Z' Z;
        // TODO : Make sure this start symbol is correct.
        StartSymbol = 'Z'; }

/// Grammar 3.20 from "Modern Compiler Implementation in ML".
let grammar_3_20 =
    // NOTE : This grammar does not include the first rule,
    // which is the production of the augmented start symbol.
    let S =
        Set.empty
        |> Set.add [|
            Symbol.Terminal "(";
            Symbol.Nonterminal 'L';
            Symbol.Terminal ")"; |]
        |> Set.add [|
            Symbol.Terminal "x"; |]

    let L =
        Set.empty
        |> Set.add [|
            Symbol.Nonterminal 'S'; |]
        |> Set.add [|
            Symbol.Nonterminal 'L';
            Symbol.Terminal ",";
            Symbol.Nonterminal 'S'; |]

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

/// Grammar 3.23 from "Modern Compiler Implementation in ML".
let grammar_3_23 =
    // NOTE : This grammar does not include the first rule,
    // which is the production of the augmented start symbol.
    let E =
        Set.empty
        |> Set.add [|
            Symbol.Nonterminal 'T';
            Symbol.Terminal "+";
            Symbol.Nonterminal 'E'; |]
        |> Set.add [|
            Symbol.Nonterminal 'T'; |]

    let T =
        Set.empty
        |> Set.add [|
            Symbol.Terminal "x"; |]

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

/// Grammar 3.26 from "Modern Compiler Implementation in ML".
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

//
let wikipedia_grammar =
    // NOTE : This grammar does not include the first rule
    // which is the production of the augmented start symbol.
    let E =
        Set.empty
        |> Set.add [|
            Symbol.Nonterminal 'T'; |]
        |> Set.add [|
            Symbol.Terminal "(";
            Symbol.Nonterminal 'E';
            Symbol.Terminal ")"; |]

    let T =
        Set.empty
        |> Set.add [|
            Symbol.Terminal "n"; |]
        |> Set.add [|
            Symbol.Terminal "+";
            Symbol.Nonterminal 'T'; |]
        |> Set.add [|
            Symbol.Nonterminal 'T';
            Symbol.Terminal "+";
            Symbol.Terminal "n"; |]

    {   Terminals =
            Set.empty
            |> Set.add "n"
            |> Set.add "+"
            |> Set.add "("
            |> Set.add ")";
        Nonterminals =
            Set.empty
            |> Set.add 'E'
            |> Set.add 'T';
        Productions =
            Map.empty
            |> Map.add 'E' E
            |> Map.add 'T' T;
        StartSymbol = 'E'; }

