(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpYacc.Tests.Predictive

open Grammars

open NUnit.Framework
open FsUnit

open FSharpYacc
open Ast
open Predictive


[<TestCase>]
let ``Analysis of Grammar 3.26`` () =
    let grammar = AugmentedGrammar.ofGrammar grammar_3_26
    let analysis = GrammarAnalysis.ofGrammar grammar

    (* Verify the nullable map. *)
    // The nullable map should have exactly the same number
    // of entries as the grammar has non-terminals.
    Set.count grammar.Nonterminals
    |> should equal analysis.Nullable.Count

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm analysis.Nullable)
    |> should be True

    // For this grammar, none of the non-terminals are nullable.
    analysis.Nullable
    |> Map.exists (fun _ v -> v)
    |> should be False

    (* Verify the FIRST sets of the nonterminals. *)
    // The map of FIRST sets should have exactly the same number
    // of entries as the grammar has non-terminals.
    Set.count grammar.Nonterminals
    |> should equal analysis.First.Count

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm analysis.First)
    |> should be True

    // Verify the entries are correct.
    let firstSet =
        Set.ofArray [|
            Terminal "*";
            Terminal "x"; |]
    grammar.Nonterminals
    |> Set.iter (fun nonterm ->
        Map.find nonterm analysis.First
        |> should equal firstSet)
        
    (* Verify the FOLLOW sets of the nonterminals. *)
    // The map of FOLLOW sets should have exactly the same number
    // of entries as the grammar has non-terminals.
    Set.count grammar.Nonterminals
    |> should equal analysis.Follow.Count

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm analysis.Follow)
    |> should be True

    // Verify the entries are correct.
    Map.find (Nonterminal 'E') analysis.Follow
    |> should equal <| Set.ofArray [|
        Terminal "="; EndOfFile; |]

    Map.find (Nonterminal 'S') analysis.Follow
    |> should equal <| Set.ofArray (
        [| EndOfFile; |] : AugmentedTerminal<string>[])

    Map.find (Nonterminal 'V') analysis.Follow
    |> should equal <| Set.ofArray [|
        Terminal "="; EndOfFile; |]

    Map.find Start analysis.Follow
    |> should equal <| Set.ofArray (
        [| EndOfFile; |] : AugmentedTerminal<string>[])

