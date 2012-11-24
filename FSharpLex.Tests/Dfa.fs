(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpLex.Tests.Dfa

open NUnit.Framework
open FsUnit
open FSharpLex
open Graph
open Regex
open Nfa


// The NFA shown in Figure 2.5 of "Basics of Compiler Construction"
let figure_2_5 =
    //
    let transitions =
        (LabeledSparseDigraph.empty, [1..8])
        // Add the vertices
        ||> List.fold (fun transitions el ->
            LabeledSparseDigraph.addVertex (LanguagePrimitives.Int32WithMeasure el) transitions)
        // Add the edges
        |> LabeledSparseDigraph.addEdge 1<_> 2<_> StateTransition.Epsilon
        |> LabeledSparseDigraph.addEdge 2<_> 3<_> (StateTransition.Symbol 'a')
        |> LabeledSparseDigraph.addEdge 3<_> 4<_> (StateTransition.Symbol 'c')
        |> LabeledSparseDigraph.addEdge 1<_> 5<_> StateTransition.Epsilon
        |> LabeledSparseDigraph.addEdge 5<_> 6<_> StateTransition.Epsilon
        |> LabeledSparseDigraph.addEdge 5<_> 7<_> StateTransition.Epsilon
        |> LabeledSparseDigraph.addEdge 6<_> 8<_> (StateTransition.Symbol 'a')
        |> LabeledSparseDigraph.addEdge 7<_> 8<_> (StateTransition.Symbol 'b')
        |> LabeledSparseDigraph.addEdge 8<_> 1<_> StateTransition.Epsilon

    // Create the NFA
    { Transitions = transitions;
        InitialState = 1<_>;
        FinalStates =
            Map.empty
            |> Map.add 4<_> 0<_>; }


//
[<TestCase>]
let figure_2_5_epsilon_closure () =
    Dfa.Dfa.epsilonClosure figure_2_5.InitialState figure_2_5
    |> should equal
    <| Set.ofArray [| 1<_>; 2<_>; 5<_>; 6<_>; 7<_>; |]


