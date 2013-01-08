(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module Graham.Tests.Analysis

open Grammars

open NUnit.Framework
open FsUnit
open TestHelpers

open Graham.Grammar
open Graham.Analysis


[<TestCase>]
let ``Analysis of Grammar 3.26`` () =
    let grammar = Appel.``Grammar 3.26``
    let predictiveSets = PredictiveSets.ofGrammar grammar

    (* Verify the nullable map. *)
    // The nullable map should have exactly the same number
    // of entries as the grammar has non-terminals.
    Assert.AreEqual (
        Set.count grammar.Nonterminals,
        predictiveSets.Nullable.Count)

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm predictiveSets.Nullable)
    |> Assert.IsTrue

    // For this grammar, none of the non-terminals are nullable.
    predictiveSets.Nullable
    |> Map.exists (fun _ v -> v)
    |> Assert.IsFalse

    (* Verify the FIRST sets of the nonterminals. *)
    // The map of FIRST sets should have exactly the same number
    // of entries as the grammar has non-terminals.
    Assert.AreEqual (
        Set.count grammar.Nonterminals,
        predictiveSets.First.Count)

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm predictiveSets.First)
    |> Assert.IsTrue

    // Verify the entries are correct.
    let firstSet =
        Set.ofArray [|
            AugmentedTerminal.Terminal "*";
            AugmentedTerminal.Terminal "x"; |]
    grammar.Nonterminals
    |> Set.iter (fun nonterm ->
        Assert.AreEqual (
            Map.find nonterm predictiveSets.First,
            firstSet))
        
    (* Verify the FOLLOW sets of the nonterminals. *)
    // The map of FOLLOW sets should have exactly the same number
    // of entries as the grammar has non-terminals.
    Assert.AreEqual (
        Set.count grammar.Nonterminals,
        predictiveSets.Follow.Count)

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm predictiveSets.Follow)
    |> Assert.IsTrue

    // Verify the entries are correct.
    Assert.AreEqual (
        Map.find (AugmentedNonterminal.Nonterminal 'E') predictiveSets.Follow,
        Set.ofArray [|
            AugmentedTerminal.Terminal "="; EndOfFile; |])

    Assert.AreEqual (
        Map.find (AugmentedNonterminal.Nonterminal 'S') predictiveSets.Follow,
        Set.ofArray (
            [| EndOfFile; |] : AugmentedTerminal<string>[]))

    Assert.AreEqual (
        Map.find (AugmentedNonterminal.Nonterminal 'V') predictiveSets.Follow,
        Set.ofArray [|
            AugmentedTerminal.Terminal "="; EndOfFile; |])

    Assert.AreEqual (
        Map.find Start predictiveSets.Follow,
        Set.ofArray (
            [| EndOfFile; |] : AugmentedTerminal<string>[]))

