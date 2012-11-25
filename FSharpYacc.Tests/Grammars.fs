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


//
[<AutoOpen>]
module private Helpers =
    /// Computes sets containing the terminals and nonterminals
    /// used within the productions of a grammar.
    let terminalsAndNonterminals productions : Set<'Token> * Set<'NonterminalId> =
        ((Set.empty, Set.empty), productions)
        ||> Map.fold (fun (terminals, nonterminals) nonterminal productions ->
            // Add the nonterminal to the set of nonterminals
            let nonterminals = Set.add nonterminal nonterminals

            ((terminals, nonterminals), productions)
            ||> Set.fold (Array.fold (fun (terminals, nonterminals) symbol ->
                // Add the current symbol to the appropriate set.
                match symbol with
                | Symbol.Terminal terminal ->
                    Set.add terminal terminals,
                    nonterminals
                | Symbol.Nonterminal nontermId ->
                    terminals,
                    Set.add nontermId nonterminals)))


/// Grammars from Andrew W. Appel's "Modern Compiler Implementation in ML".
module Appel =
    /// Grammar 3.5 from "Modern Compiler Implementation in ML".
    let ``Grammar 3.5`` =
        let E =
            Set.empty
            |> Set.add [|
                Symbol.Terminal "id"; |]
            |> Set.add [|
                Symbol.Terminal "num"; |]
            |> Set.add [|
                Symbol.Nonterminal 'E';
                Symbol.Terminal "*";
                Symbol.Nonterminal 'E'; |]
            |> Set.add [|
                Symbol.Nonterminal 'E';
                Symbol.Terminal "/";
                Symbol.Nonterminal 'E'; |]
            |> Set.add [|
                Symbol.Nonterminal 'E';
                Symbol.Terminal "+";
                Symbol.Nonterminal 'E'; |]
            |> Set.add [|
                Symbol.Nonterminal 'E';
                Symbol.Terminal "-";
                Symbol.Nonterminal 'E'; |]
            |> Set.add [|
                Symbol.Terminal "(";
                Symbol.Nonterminal 'E';
                Symbol.Terminal ")"; |]

        let productions =
            Map.empty
            |> Map.add 'E' E

        let terminals, nonterminals = terminalsAndNonterminals productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions;
            StartSymbol = 'E'; }

    /// Grammar 3.8 from "Modern Compiler Implementation in ML".
    let ``Grammar 3.8`` =
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

        let productions =
            Map.empty
            |> Map.add 'E' E
            |> Map.add 'T' T
            |> Map.add 'F' F

        let terminals, nonterminals = terminalsAndNonterminals productions

        // Create the grammar from the productions.
        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions;
            // TODO : Make sure this start symbol is correct.
            StartSymbol = 'F'; }

    /// Grammar 3.12 from "Modern Compiler Implementation in ML".
    let ``Grammar 3.12`` =
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

        let productions =
            Map.empty
            |> Map.add 'X' X
            |> Map.add 'Y' Y
            |> Map.add 'Z' Z

        let terminals, nonterminals = terminalsAndNonterminals productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions;
            // TODO : Make sure this start symbol is correct.
            StartSymbol = 'Z'; }

    /// Grammar 3.20 from "Modern Compiler Implementation in ML".
    let ``Grammar 3.20`` =
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

        let productions =
            Map.empty
            |> Map.add 'L' L
            |> Map.add 'S' S

        let terminals, nonterminals = terminalsAndNonterminals productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions;
            StartSymbol = 'S'; }

    /// Grammar 3.23 from "Modern Compiler Implementation in ML".
    let ``Grammar 3.23`` =
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

        let productions =
            Map.empty
            |> Map.add 'E' E
            |> Map.add 'T' T

        let terminals, nonterminals = terminalsAndNonterminals productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions;
            StartSymbol = 'E'; }

    /// Grammar 3.26 from "Modern Compiler Implementation in ML".
    let ``Grammar 3.26`` =
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

        let productions =
            Map.empty
            |> Map.add 'S' S
            |> Map.add 'E' E
            |> Map.add 'V' V

        let terminals, nonterminals = terminalsAndNonterminals productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions;
            StartSymbol = 'S'; }

    /// Grammar 3.30 from "Modern Compiler Implementation in ML".
    let ``Grammar 3.30`` =
        // prog
        let P =
            Set.empty
            |> Set.add [|
                Symbol.Nonterminal 'P'; |]

        // stm
        let S =
            Set.empty
            |> Set.add [|
                Symbol.Terminal "id";
                Symbol.Terminal ":=";
                Symbol.Terminal "id"; |]
            |> Set.add [|
                Symbol.Terminal "while";
                Symbol.Terminal "id";
                Symbol.Terminal "do";
                Symbol.Nonterminal 'S'; |]
            |> Set.add [|
                Symbol.Terminal "begin";
                Symbol.Nonterminal 'L';
                Symbol.Terminal "end"; |]
            |> Set.add [|
                Symbol.Terminal "if";
                Symbol.Terminal "id";
                Symbol.Terminal "then";
                Symbol.Nonterminal 'S'; |]
            |> Set.add [|
                Symbol.Terminal "if";
                Symbol.Terminal "id";
                Symbol.Terminal "then";
                Symbol.Nonterminal 'S';
                Symbol.Terminal "else";
                Symbol.Nonterminal 'S'; |]

        // stmlist
        let L =
            Set.empty
            |> Set.add [|
                Symbol.Nonterminal 'S'; |]
            |> Set.add [|
                Symbol.Nonterminal 'L';
                Symbol.Terminal ";";
                Symbol.Nonterminal 'S'; |]

        let productions =
            Map.empty
            |> Map.add 'P' P
            |> Map.add 'S' S
            |> Map.add 'L' L

        let terminals, nonterminals = terminalsAndNonterminals productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions;
            StartSymbol = 'P'; }

    /// Grammar 4.6 from "Modern Compiler Implementation in ML".
    let ``Grammar 4.6`` =
        let S =
            Set.empty
            |> Set.add [|
                Symbol.Nonterminal 'S';
                Symbol.Terminal ";";
                Symbol.Nonterminal 'S'; |]
            |> Set.add [|
                Symbol.Terminal "id";
                Symbol.Terminal ":=";
                Symbol.Nonterminal 'E'; |]
            |> Set.add [|
                Symbol.Terminal "print";
                Symbol.Nonterminal 'L'; |]

        let E =
            Set.empty
            |> Set.add [|
                Symbol.Terminal "id"; |]
            |> Set.add [|
                Symbol.Terminal "num"; |]
            |> Set.add [|
                Symbol.Nonterminal 'E';
                Symbol.Nonterminal 'B';
                Symbol.Nonterminal 'E'; |]
            |> Set.add [|
                Symbol.Nonterminal 'S';
                Symbol.Terminal ",";
                Symbol.Nonterminal 'E'; |]

        let L =
            Set.empty
            |> Set.add [| |]    // Empty production
            |> Set.add [|
                Symbol.Nonterminal 'L';
                Symbol.Nonterminal 'E'; |]

        let B =
            Set.empty
            |> Set.add [|
                Symbol.Terminal "+"; |]
            |> Set.add [|
                Symbol.Terminal "-"; |]
            |> Set.add [|
                Symbol.Terminal "*"; |]
            |> Set.add [|
                Symbol.Terminal "/"; |]

        let productions =
            Map.empty
            |> Map.add 'S' S
            |> Map.add 'E' E
            |> Map.add 'L' L
            |> Map.add 'B' B

        let terminals, nonterminals = terminalsAndNonterminals productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions;
            StartSymbol = 'S'; }


