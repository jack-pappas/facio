(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

/// Contains patterns for testing NFA and DFA generation.
module FSharpLex.Tests.Patterns

open FSharpLex
open Graph
open Regex
open Nfa


//
[<AutoOpen>]
module private Helpers =
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

// a(b|c)*
let ``a(b|c)*`` =
    Sequence (
        Symbol 'a',
        ZeroOrMore (
            Alternate (
                Symbol 'b',
                Symbol 'c')))

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



