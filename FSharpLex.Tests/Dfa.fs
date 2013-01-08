(*
Copyright (c) 2012-2013, Jack Pappas
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


//
[<TestCase>]
let figure_2_5_epsilon_closure () =
    Dfa.Dfa.epsilonClosure figure_2_5.InitialState figure_2_5
    |> should equal
    <| Set.ofArray [| 1<_>; 2<_>; 5<_>; 6<_>; 7<_>; |]

//let figure_2_5_dfa =
//    Dfa.ofNfa figure_2_5
//
//let id_dfa =
//    Dfa.ofNfa id_nfa
//
//let abc_dfa =
//    Dfa.ofNfa abc_nfa
//
//let abac_dfa =
//    Dfa.ofNfa abac_nfa

//let combined_dfa =
//    Dfa.ofNfa combined_nfa
//
////
//"abaccbaaabcaba"
//|> Dfa.tokenize combined_dfa
////|> Dfa.tokenize abc_dfa
//|> Seq.iter (function
//    | Choice1Of2 (regexIndex, token) ->
//        printfn "Matched regex #%i: '%s'" (int regexIndex) (System.String token)
//    | Choice2Of2 invalidToken ->
//        printfn "Rejected: '%s'" (System.String invalidToken)
//    )