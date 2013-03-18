(*

Copyright 2012-2013 Jack Pappas

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

module Graham.Tests.Analysis

open NUnit.Framework
open FsUnit
open TestHelpers

open Graham.Grammar
open Graham.Analysis


[<TestCase>]
let ``Analysis of Grammar 3.26`` () =
    let grammar = Grammars.Appel.``Grammar 3.26``
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

