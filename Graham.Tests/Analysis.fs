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

open Graham.Grammar
open Graham.Analysis
open Tests.Graham.Grammars


[<TestCase>]
let ``Analysis of Grammar 3.26`` () =
    let grammar = Appel.``Grammar 3.26``
    let predictiveSets = PredictiveSets.ofGrammar grammar

    (* Verify the nullable map. *)
    // The nullable map should have exactly the same number
    // of entries as the grammar has non-terminals.
    Map.count predictiveSets.Nullable
    |> assertEqual (Set.count grammar.Nonterminals)

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm predictiveSets.Nullable)
    |> assertTrue

    // For this grammar, none of the non-terminals are nullable.
    predictiveSets.Nullable
    |> Map.exists (fun _ v -> v)
    |> assertFalse

    (* Verify the FIRST sets of the nonterminals. *)
    // The map of FIRST sets should have exactly the same number
    // of entries as the grammar has non-terminals.
    Map.count predictiveSets.First
    |> assertEqual (Set.count grammar.Nonterminals)

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm predictiveSets.First)
    |> assertTrue

    // Verify the entries are correct.
    let firstSet =
        Set.ofArray [|
            AugmentedTerminal.Terminal "*";
            AugmentedTerminal.Terminal "x"; |]

    grammar.Nonterminals
    |> Set.iter (fun nonterm ->
        firstSet
        |> assertEqual (Map.find nonterm predictiveSets.First))
        
    (* Verify the FOLLOW sets of the nonterminals. *)
    // The map of FOLLOW sets should have exactly the same number
    // of entries as the grammar has non-terminals.
    Map.count predictiveSets.Follow
    |> assertEqual (Set.count grammar.Nonterminals)

    // All non-terminals should have an entry.
    grammar.Nonterminals
    |> Set.forall (fun nonterm ->
        Map.containsKey nonterm predictiveSets.Follow)
    |> assertTrue

    // Verify the entries are correct.
    [| AugmentedTerminal.Terminal "="; EndOfFile; |]
    |> Set.ofArray
    |> assertEqual
        (Map.find (AugmentedNonterminal.Nonterminal 'E') predictiveSets.Follow)

    ([| EndOfFile; |] : AugmentedTerminal<string>[])
    |> Set.ofArray
    |> assertEqual
        (Map.find (AugmentedNonterminal.Nonterminal 'S') predictiveSets.Follow)

    [| AugmentedTerminal.Terminal "="; EndOfFile; |]
    |> Set.ofArray
    |> assertEqual
        (Map.find (AugmentedNonterminal.Nonterminal 'V') predictiveSets.Follow)

    ([| EndOfFile; |] : AugmentedTerminal<string>[])
    |> Set.ofArray
    |> assertEqual
        (Map.find Start predictiveSets.Follow)
