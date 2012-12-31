(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module Graham.Tests.Predictive

open Grammars

open NUnit.Framework
open FsUnit

open Graham.Grammar
open Graham.Analysis


[<TestCase>]
let ``Analysis of Grammar 3.26`` () =
    let grammar = AugmentedGrammar.ofGrammar Appel.``Grammar 3.26``
    let predictiveSets = PredictiveSets.ofGrammar grammar

    (* Verify the nullable map. *)
    // The nullable map should have exactly the same number
    // of entries as the grammar has non-terminals.
    Set.count grammar.Nonterminals
    |> should equal predictiveSets.Nullable.Count

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm predictiveSets.Nullable)
    |> should be True

    // For this grammar, none of the non-terminals are nullable.
    predictiveSets.Nullable
    |> Map.exists (fun _ v -> v)
    |> should be False

    (* Verify the FIRST sets of the nonterminals. *)
    // The map of FIRST sets should have exactly the same number
    // of entries as the grammar has non-terminals.
    Set.count grammar.Nonterminals
    |> should equal predictiveSets.First.Count

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm predictiveSets.First)
    |> should be True

    // Verify the entries are correct.
    let firstSet =
        Set.ofArray [|
            Terminal "*";
            Terminal "x"; |]
    grammar.Nonterminals
    |> Set.iter (fun nonterm ->
        Map.find nonterm predictiveSets.First
        |> should equal firstSet)
        
    (* Verify the FOLLOW sets of the nonterminals. *)
    // The map of FOLLOW sets should have exactly the same number
    // of entries as the grammar has non-terminals.
    Set.count grammar.Nonterminals
    |> should equal predictiveSets.Follow.Count

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm predictiveSets.Follow)
    |> should be True

    // Verify the entries are correct.
    Map.find (Nonterminal 'E') predictiveSets.Follow
    |> should equal <| Set.ofArray [|
        Terminal "="; EndOfFile; |]

    Map.find (Nonterminal 'S') predictiveSets.Follow
    |> should equal <| Set.ofArray (
        [| EndOfFile; |] : AugmentedTerminal<string>[])

    Map.find (Nonterminal 'V') predictiveSets.Follow
    |> should equal <| Set.ofArray [|
        Terminal "="; EndOfFile; |]

    Map.find Start predictiveSets.Follow
    |> should equal <| Set.ofArray (
        [| EndOfFile; |] : AugmentedTerminal<string>[])

