(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module Graham.Tests.Tables

open Grammars

open NUnit.Framework
open FsUnit

open Graham
open Ast
open Predictive
open LR


[<TestCase>]
let ``LR(0) table for Grammar 3.20`` () =
    let table = LR.Lr0.createTable Appel.``Grammar 3.20``
    
    let expectedTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 2<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'S') (
            Set.ofArray [| Goto 4<_>; |])

        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal <| Terminal ")") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal <| Terminal ",") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (3<ParserStateIdentifier>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (3<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 2<_>; |])
        |> Map.add (3<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'L') (
            Set.ofArray [| Goto 6<_>; |])
        |> Map.add (3<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'S') (
            Set.ofArray [| Goto 5<_>; |])

        |> Map.add (4<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Accept; |])

        |> Map.add (5<ParserStateIdentifier>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Terminal <| Terminal ")") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Terminal <| Terminal ",") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 2<_>; |])

        |> Map.add (6<ParserStateIdentifier>, Symbol.Terminal <| Terminal ")") (
            Set.ofArray [| Shift 8<_>; |])
        |> Map.add (6<ParserStateIdentifier>, Symbol.Terminal <| Terminal ",") (
            Set.ofArray [| Shift 7<_>; |])

        |> Map.add (7<ParserStateIdentifier>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (7<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 2<_>; |])
        |> Map.add (7<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'S') (
            Set.ofArray [| Goto 9<_>; |])

        |> Map.add (8<ParserStateIdentifier>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (8<ParserStateIdentifier>, Symbol.Terminal <| Terminal ")") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (8<ParserStateIdentifier>, Symbol.Terminal <| Terminal ",") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (8<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (8<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

        |> Map.add (9<ParserStateIdentifier>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (9<ParserStateIdentifier>, Symbol.Terminal <| Terminal ")") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (9<ParserStateIdentifier>, Symbol.Terminal <| Terminal ",") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (9<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (9<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 4<_>; |])

    // Verify the table.
    table.Table
    |> should equal expectedTable

[<TestCase>]
let ``LR(0) table for Grammar 3.23`` () =
    let table = LR.Lr0.createTable Appel.``Grammar 3.23``
    // table should have 6 states and 3 rules

    let expectedTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 4<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'T') (
            Set.ofArray [| Goto 2<_>; |])

        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal <| Terminal "+") (
            Set.ofArray [| Shift 5<_>; Reduce 1<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (3<ParserStateIdentifier>, Symbol.Terminal <| Terminal "+") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (3<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (3<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 2<_>; |])

        |> Map.add (4<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Accept; |])

        |> Map.add (5<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 6<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'T') (
            Set.ofArray [| Goto 2<_>; |])

        |> Map.add (6<ParserStateIdentifier>, Symbol.Terminal <| Terminal "+") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (6<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (6<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

    // Verify the table.
    table.Table
    |> should equal expectedTable

[<TestCase>]
let ``SLR table for Grammar 3.23`` () =
    let table = LR.Slr.createTable Appel.``Grammar 3.23``

    let expectedTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 4<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'T') (
            Set.ofArray [| Goto 2<_>; |])

        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal <| Terminal "+") (
            Set.ofArray [| Shift 5<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (3<ParserStateIdentifier>, Symbol.Terminal <| Terminal "+") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (3<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 2<_>; |])

        |> Map.add (4<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Accept; |])

        |> Map.add (5<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 6<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'T') (
            Set.ofArray [| Goto 2<_>; |])

        |> Map.add (6<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

    // Verify the table.
    table.Table
    |> should equal expectedTable

[<TestCase>]
let ``LR(1) table for Grammar 3.26`` () =
    let table = LR.Lr1.createTable Appel.``Grammar 3.26``

    let expectedTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 5<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 4<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 3<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'S') (
            Set.ofArray [| Goto 6<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 2<_>; |])

        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Shift 9<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (3<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 2<_>; |])

        |> Map.add (4<ParserStateIdentifier>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (4<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

        |> Map.add (5<ParserStateIdentifier>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 5<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 4<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 8<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 7<_>; |])

        |> Map.add (6<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Accept; |])

        |> Map.add (7<ParserStateIdentifier>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (7<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (8<ParserStateIdentifier>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (8<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 4<_>; |])

        |> Map.add (9<ParserStateIdentifier>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 13<_>; |])
        |> Map.add (9<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 12<_>; |])
        |> Map.add (9<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 11<_>; |])
        |> Map.add (9<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 10<_>; |])

        |> Map.add (10<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (11<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 5<_>; |])

        |> Map.add (12<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

        |> Map.add (13<ParserStateIdentifier>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 13<_>; |])
        |> Map.add (13<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 12<_>; |])
        |> Map.add (13<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 14<_>; |])
        |> Map.add (13<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 10<_>; |])
        
        |> Map.add (14<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 4<_>; |])

    // Verify the table.
    table.Table
    |> should equal expectedTable

[<TestCase>]
let ``LALR(1) table for Grammar 3.26`` () =
    let table = LR.Lr1.createCompressedTable Appel.``Grammar 3.26``

    let expectedTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 1<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 8<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 9<_>; |])
        |> Map.add (1<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 4<_>; |])

        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 1<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 8<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 6<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'S') (
            Set.ofArray [| Goto 10<_>; |])
        |> Map.add (2<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 5<_>; |])

        |> Map.add (3<ParserStateIdentifier>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 1<_>; |])
        |> Map.add (3<ParserStateIdentifier>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 8<_>; |])
        |> Map.add (3<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 7<_>; |])
        |> Map.add (3<ParserStateIdentifier>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 4<_>; |])

        |> Map.add (4<ParserStateIdentifier>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (4<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (5<ParserStateIdentifier>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (5<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (6<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 2<_>; |])

        |> Map.add (7<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 5<_>; |])

        |> Map.add (8<ParserStateIdentifier>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (8<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

        |> Map.add (9<ParserStateIdentifier>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (9<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 4<_>; |])

        |> Map.add (10<ParserStateIdentifier>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Accept; |])

    // Verify the table.
    table.Table
    |> should equal expectedTable

