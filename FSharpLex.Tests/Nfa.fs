(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpLex.Tests.Nfa

open NUnit.Framework
open FsUnit
open Patterns
open FSharpLex
open Graph
open Regex
open Nfa



let id_nfa =
    Nfa.ofRegex id_regex

let abc_nfa =
    Nfa.ofRegex ``a(b|c)*``

let abac_nfa =
    Nfa.ofRegex ``(a|b)*ac``


// The NFA shown in Figure 2.5 of "Basics of Compiler Construction"
let figure_2_5 =
    //
    let transitions =
        (LexerNfaGraph.empty, [1..8])
        // Add the vertices
        ||> List.fold (fun transitions el ->
            transitions
            |> LexerNfaGraph.createVertex
            |> snd)
        // Add the edges
        |> LexerNfaGraph.addEpsilonEdge 1<_> 2<_>
        |> LexerNfaGraph.addSymbolEdge 2<_> 3<_> 'a'
        |> LexerNfaGraph.addSymbolEdge 3<_> 4<_> 'c'
        |> LexerNfaGraph.addEpsilonEdge 1<_> 5<_>
        |> LexerNfaGraph.addEpsilonEdge 5<_> 6<_>
        |> LexerNfaGraph.addEpsilonEdge 5<_> 7<_>
        |> LexerNfaGraph.addSymbolEdge 6<_> 8<_> 'a'
        |> LexerNfaGraph.addSymbolEdge 7<_> 8<_> 'b'
        |> LexerNfaGraph.addEpsilonEdge 8<_> 1<_>

    // Create the NFA
    { Transitions = transitions;
        InitialState = 1<_>;
        FinalStates =
            Map.empty
            |> Map.add 4<_> 0<_>; }


//// TEST : Compile some regexes into a single NFA.
//let combined_nfa =
//    Nfa.ofRegexes [|
//        ``a(b|c)*``;
//        ``(a|b)*ac``;
//        |]
