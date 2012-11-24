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
    let table = Tables.Lr0.createTable grammar_3_20
    
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
    let table = Tables.Lr0.createTable grammar_3_23
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
    let table = Tables.Slr.createTable grammar_3_23

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


