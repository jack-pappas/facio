(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpLex.Program

open Graph
open Nfa
open Regex


//
let charSetRegex (set : Set<char>) =
    let minElement = Set.minElement set
    let set = Set.remove minElement set
    (Symbol minElement, set)
    ||> Set.fold (fun regex symbol ->
        Alternate (
            regex,
            Symbol symbol))

// ID
// [a-z][a-z0-9]*
let id_regex =
    let ``[a-z]`` =
        seq {'a' .. 'z'}
        |> Set.ofSeq
        |> charSetRegex

    let ``[a-z0-9]`` =
        seq {'a' .. 'z'}
        |> Seq.append (seq {'0' .. '9'})
        |> Set.ofSeq
        |> charSetRegex

    Sequence (
        ``[a-z]``,
        ZeroOrMore ``[a-z0-9]``)

let id_nfa =
    Nfa.ofRegex id_regex

let id_dfa =
    Dfa.ofNfa id_nfa
    

// a(b|c)*
let ``a(b|c)*`` =
    Sequence (
        Symbol 'a',
        ZeroOrMore (
            Alternate (
                Symbol 'b',
                Symbol 'c')))

let abc_nfa =
    Nfa.ofRegex ``a(b|c)*``

let abc_dfa =
    Dfa.ofNfa abc_nfa


// (a|b)*ac
let ``(a|b)*ac`` =
    let ``(a|b)*`` =
        Alternate (
            Symbol 'a',
            Symbol 'b')
        |> ZeroOrMore

    Sequence (
        ``(a|b)*``,
        Sequence (
            Symbol 'a',
            Symbol 'c'))

let abac_nfa =
    Nfa.ofRegex ``(a|b)*ac``

let abac_dfa =
    Dfa.ofNfa abac_nfa


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

let figure_2_5_dfa =
    Dfa.ofNfa figure_2_5


// TEST : Compile some regexes into a single NFA.
let combined_nfa =
    Nfa.ofRegexes [|
        ``a(b|c)*``;
        ``(a|b)*ac``;
        |]

let combined_dfa =
    Dfa.ofNfa combined_nfa

//
"abaccbaaabcaba"
|> Dfa.tokenize combined_dfa
//|> Dfa.tokenize abc_dfa
|> Seq.iter (function
    | Choice1Of2 (regexIndex, token) ->
        printfn "Matched regex #%i: '%s'" (int regexIndex) (System.String token)
    | Choice2Of2 invalidToken ->
        printfn "Rejected: '%s'" (System.String invalidToken)
    )


printfn "Press any key to exit..."
System.Console.ReadKey ()
|> ignore

