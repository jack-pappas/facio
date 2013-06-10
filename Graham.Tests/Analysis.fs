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

module Tests.Graham.Analysis

open NUnit.Framework
open FsUnit

open Graham
open Graham.Analysis
open Tests.Graham.Grammars


[<TestCase>]
let ``Analysis of Grammar 3.26`` () =
    let taggedGrammar =
        let grammar = Appel.``Grammar 3.26``
        TaggedGrammar.ofGrammar grammar
    let predictiveSets = PredictiveSets.ofGrammar taggedGrammar

    (* Verify the nullable map. *)
    // The nullable map should have exactly the same number
    // of entries as the grammar has non-terminals.
    TagMap.count predictiveSets.Nullable
    |> assertEqual (TagBimap.count taggedGrammar.Nonterminals)

    // All non-terminals should have an entry.
    taggedGrammar.Nonterminals
    |> TagBimap.forall (fun nonterminalIndex _ ->
        TagMap.containsKey nonterminalIndex predictiveSets.Nullable)
    |> assertTrue

    // For this grammar, none of the non-terminals are nullable.
    predictiveSets.Nullable
    |> TagMap.exists (fun _ v -> v)
    |> assertFalse

    (* Verify the FIRST sets of the nonterminals. *)
    // The map of FIRST sets should have exactly the same number
    // of entries as the grammar has non-terminals.
    TagMap.count predictiveSets.First
    |> assertEqual (TagBimap.count taggedGrammar.Nonterminals)

    // All non-terminals should have an entry.
    taggedGrammar.Nonterminals
    |> TagBimap.forall (fun nonterminalIndex _ ->
        TagMap.containsKey nonterminalIndex predictiveSets.First)
    |> assertTrue

    // Verify the entries are correct.
    let firstSet =
        [|  AugmentedTerminal.Terminal "*";
            AugmentedTerminal.Terminal "x"; |]
        |> Set.ofArray 
        |> Set.map (fun terminal ->
            TagBimap.findValue terminal taggedGrammar.Terminals)
        |> TagSet.ofSet

    taggedGrammar.Nonterminals
    |> TagBimap.iter (fun nonterminalIndex _ ->
        firstSet
        |> assertEqual (TagMap.find nonterminalIndex predictiveSets.First))
        
    (* Verify the FOLLOW sets of the nonterminals. *)
    // The map of FOLLOW sets should have exactly the same number
    // of entries as the grammar has non-terminals.
    TagMap.count predictiveSets.Follow
    |> assertEqual (TagBimap.count taggedGrammar.Nonterminals)

    // All non-terminals should have an entry.
    taggedGrammar.Nonterminals
    |> TagBimap.forall (fun nonterminalIndex _ ->
        TagMap.containsKey nonterminalIndex predictiveSets.Follow)
    |> assertTrue

    // Verify the entries are correct.
    [| AugmentedTerminal.Terminal "="; EndOfFile; |]
    |> Array.map (fun terminal ->
        TagBimap.findValue terminal taggedGrammar.Terminals)
    |> TagSet.ofArray
    |> assertEqual
        (let nonterminalIndex = TagBimap.findValue (AugmentedNonterminal.Nonterminal 'E') taggedGrammar.Nonterminals in
         TagMap.find nonterminalIndex predictiveSets.Follow)

    ([| EndOfFile; |] : AugmentedTerminal<string>[])
    |> Array.map (fun terminal ->
        TagBimap.findValue terminal taggedGrammar.Terminals)
    |> TagSet.ofArray
    |> assertEqual
        (let nonterminalIndex = TagBimap.findValue (AugmentedNonterminal.Nonterminal 'S') taggedGrammar.Nonterminals in
         TagMap.find nonterminalIndex predictiveSets.Follow)

    [| AugmentedTerminal.Terminal "="; EndOfFile; |]
    |> Array.map (fun terminal ->
        TagBimap.findValue terminal taggedGrammar.Terminals)
    |> TagSet.ofArray
    |> assertEqual
        (let nonterminalIndex = TagBimap.findValue (AugmentedNonterminal.Nonterminal 'V') taggedGrammar.Nonterminals in
         TagMap.find nonterminalIndex predictiveSets.Follow)

    ([| EndOfFile; |] : AugmentedTerminal<string>[])
    |> Array.map (fun terminal ->
        TagBimap.findValue terminal taggedGrammar.Terminals)
    |> TagSet.ofArray
    |> assertEqual
        (let nonterminalIndex = TagBimap.findValue Start taggedGrammar.Nonterminals in
         TagMap.find nonterminalIndex predictiveSets.Follow)
