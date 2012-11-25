(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpYacc.Tests.Tables

open Grammars

open NUnit.Framework
open FsUnit

open FSharpYacc
open Ast
open Predictive
open Tables


[<TestCase>]
let ``LR(0) table for Grammar 3.20`` () =
    let table = Tables.Lr0.createTable Appel.``Grammar 3.20``
    
    let expectedTable =
        Map.empty
        |> Map.add (1<LrParserState>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 2<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Nonterminal <| Nonterminal 'S') (
            Set.ofArray [| Goto 4<_>; |])

        |> Map.add (2<LrParserState>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Terminal <| Terminal ")") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Terminal <| Terminal ",") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (3<LrParserState>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (3<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 2<_>; |])
        |> Map.add (3<LrParserState>, Symbol.Nonterminal <| Nonterminal 'L') (
            Set.ofArray [| Goto 6<_>; |])
        |> Map.add (3<LrParserState>, Symbol.Nonterminal <| Nonterminal 'S') (
            Set.ofArray [| Goto 5<_>; |])

        |> Map.add (4<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Accept; |])

        |> Map.add (5<LrParserState>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Terminal <| Terminal ")") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Terminal <| Terminal ",") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 2<_>; |])

        |> Map.add (6<LrParserState>, Symbol.Terminal <| Terminal ")") (
            Set.ofArray [| Shift 8<_>; |])
        |> Map.add (6<LrParserState>, Symbol.Terminal <| Terminal ",") (
            Set.ofArray [| Shift 7<_>; |])

        |> Map.add (7<LrParserState>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (7<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 2<_>; |])
        |> Map.add (7<LrParserState>, Symbol.Nonterminal <| Nonterminal 'S') (
            Set.ofArray [| Goto 9<_>; |])

        |> Map.add (8<LrParserState>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (8<LrParserState>, Symbol.Terminal <| Terminal ")") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (8<LrParserState>, Symbol.Terminal <| Terminal ",") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (8<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (8<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

        |> Map.add (9<LrParserState>, Symbol.Terminal <| Terminal "(") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (9<LrParserState>, Symbol.Terminal <| Terminal ")") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (9<LrParserState>, Symbol.Terminal <| Terminal ",") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (9<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (9<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 4<_>; |])

    // Verify the table.
    table.Table
    |> should equal expectedTable

[<TestCase>]
let ``LR(0) table for Grammar 3.23`` () =
    let table = Tables.Lr0.createTable Appel.``Grammar 3.23``
    // table should have 6 states and 3 rules

    let expectedTable =
        Map.empty
        |> Map.add (1<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 4<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Nonterminal <| Nonterminal 'T') (
            Set.ofArray [| Goto 2<_>; |])

        |> Map.add (2<LrParserState>, Symbol.Terminal <| Terminal "+") (
            Set.ofArray [| Shift 5<_>; Reduce 1<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (3<LrParserState>, Symbol.Terminal <| Terminal "+") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (3<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (3<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 2<_>; |])

        |> Map.add (4<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Accept; |])

        |> Map.add (5<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 6<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Nonterminal <| Nonterminal 'T') (
            Set.ofArray [| Goto 2<_>; |])

        |> Map.add (6<LrParserState>, Symbol.Terminal <| Terminal "+") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (6<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (6<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

    // Verify the table.
    table.Table
    |> should equal expectedTable

[<TestCase>]
let ``SLR table for Grammar 3.23`` () =
    let table = Tables.Slr.createTable Appel.``Grammar 3.23``

    let expectedTable =
        Map.empty
        |> Map.add (1<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 4<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Nonterminal <| Nonterminal 'T') (
            Set.ofArray [| Goto 2<_>; |])

        |> Map.add (2<LrParserState>, Symbol.Terminal <| Terminal "+") (
            Set.ofArray [| Shift 5<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (3<LrParserState>, Symbol.Terminal <| Terminal "+") (
            Set.ofArray [| Reduce 2<_>; |])
        |> Map.add (3<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 2<_>; |])

        |> Map.add (4<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Accept; |])

        |> Map.add (5<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 6<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Nonterminal <| Nonterminal 'T') (
            Set.ofArray [| Goto 2<_>; |])

        |> Map.add (6<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

    // Verify the table.
    table.Table
    |> should equal expectedTable

[<TestCase>]
let ``LR(1) table for Grammar 3.26`` () =
    let table = Tables.Lr1.createTable Appel.``Grammar 3.26``

    let expectedTable =
        Map.empty
        |> Map.add (1<LrParserState>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 5<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 4<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 3<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Nonterminal <| Nonterminal 'S') (
            Set.ofArray [| Goto 6<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 2<_>; |])

        |> Map.add (2<LrParserState>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Shift 9<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (3<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 2<_>; |])

        |> Map.add (4<LrParserState>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (4<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

        |> Map.add (5<LrParserState>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 5<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 4<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 8<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 7<_>; |])

        |> Map.add (6<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Accept; |])

        |> Map.add (7<LrParserState>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (7<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (8<LrParserState>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (8<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 4<_>; |])

        |> Map.add (9<LrParserState>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 13<_>; |])
        |> Map.add (9<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 12<_>; |])
        |> Map.add (9<LrParserState>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 11<_>; |])
        |> Map.add (9<LrParserState>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 10<_>; |])

        |> Map.add (10<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (11<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 5<_>; |])

        |> Map.add (12<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

        |> Map.add (13<LrParserState>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 13<_>; |])
        |> Map.add (13<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 12<_>; |])
        |> Map.add (13<LrParserState>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 14<_>; |])
        |> Map.add (13<LrParserState>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 10<_>; |])
        
        |> Map.add (14<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 4<_>; |])

    // Verify the table.
    table.Table
    |> should equal expectedTable

[<TestCase>]
let ``LALR(1) table for Grammar 3.26`` () =
    let table = Tables.Lr1.createCompressedTable Appel.``Grammar 3.26``

    let expectedTable =
        Map.empty
        |> Map.add (1<LrParserState>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 1<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 8<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 9<_>; |])
        |> Map.add (1<LrParserState>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 4<_>; |])

        |> Map.add (2<LrParserState>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 1<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 8<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 6<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Nonterminal <| Nonterminal 'S') (
            Set.ofArray [| Goto 10<_>; |])
        |> Map.add (2<LrParserState>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 5<_>; |])

        |> Map.add (3<LrParserState>, Symbol.Terminal <| Terminal "*") (
            Set.ofArray [| Shift 1<_>; |])
        |> Map.add (3<LrParserState>, Symbol.Terminal <| Terminal "x") (
            Set.ofArray [| Shift 8<_>; |])
        |> Map.add (3<LrParserState>, Symbol.Nonterminal <| Nonterminal 'E') (
            Set.ofArray [| Goto 7<_>; |])
        |> Map.add (3<LrParserState>, Symbol.Nonterminal <| Nonterminal 'V') (
            Set.ofArray [| Goto 4<_>; |])

        |> Map.add (4<LrParserState>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 1<_>; |])
        |> Map.add (4<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (5<LrParserState>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Shift 3<_>; |])
        |> Map.add (5<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 1<_>; |])

        |> Map.add (6<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 2<_>; |])

        |> Map.add (7<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 5<_>; |])

        |> Map.add (8<LrParserState>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 3<_>; |])
        |> Map.add (8<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 3<_>; |])

        |> Map.add (9<LrParserState>, Symbol.Terminal <| Terminal "=") (
            Set.ofArray [| Reduce 4<_>; |])
        |> Map.add (9<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Reduce 4<_>; |])

        |> Map.add (10<LrParserState>, Symbol.Terminal EndOfFile) (
            Set.ofArray [| Accept; |])

    // Verify the table.
    table.Table
    |> should equal expectedTable

