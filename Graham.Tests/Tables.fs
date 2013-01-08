(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module Graham.Tests.Tables

open Grammars

open NUnit.Framework
open FsUnit

open Graham.Grammar
open Graham.Analysis
open Graham.LR


[<TestCase>]
let ``LR(0) table for Grammar 3.20`` () =
    let lr0ParserTable = Lr0.createTable Appel.``Grammar 3.20``
    
    let expectedActionTable : Map<TerminalTransition<AugmentedTerminal<string>>, LrParserActionSet> =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, AugmentedTerminal.Terminal "(") (Action <| Shift 3<_>)
        |> Map.add (1<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 2<_>)

        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.Terminal "(") (Action <| Reduce 1<_>)
        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.Terminal ")") (Action <| Reduce 1<_>)
        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.Terminal ",") (Action <| Reduce 1<_>)
        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Reduce 1<_>)
        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 1<_>)

        |> Map.add (3<ParserStateIdentifier>, AugmentedTerminal.Terminal "(") (Action <| Shift 3<_>)
        |> Map.add (3<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 2<_>)

        |> Map.add (4<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action Accept)

        |> Map.add (5<ParserStateIdentifier>, AugmentedTerminal.Terminal "(") (Action <| Reduce 2<_>)
        |> Map.add (5<ParserStateIdentifier>, AugmentedTerminal.Terminal ")") (Action <| Reduce 2<_>)
        |> Map.add (5<ParserStateIdentifier>, AugmentedTerminal.Terminal ",") (Action <| Reduce 2<_>)
        |> Map.add (5<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Reduce 2<_>)
        |> Map.add (5<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 2<_>)

        |> Map.add (6<ParserStateIdentifier>, AugmentedTerminal.Terminal ")") (Action <| Shift 8<_>)
        |> Map.add (6<ParserStateIdentifier>, AugmentedTerminal.Terminal ",") (Action <| Shift 7<_>)

        |> Map.add (7<ParserStateIdentifier>, AugmentedTerminal.Terminal "(") (Action <| Shift 3<_>)
        |> Map.add (7<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 2<_>)

        |> Map.add (8<ParserStateIdentifier>, AugmentedTerminal.Terminal "(") (Action <| Reduce 3<_>)
        |> Map.add (8<ParserStateIdentifier>, AugmentedTerminal.Terminal ")") (Action <| Reduce 3<_>)
        |> Map.add (8<ParserStateIdentifier>, AugmentedTerminal.Terminal ",") (Action <| Reduce 3<_>)
        |> Map.add (8<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Reduce 3<_>)
        |> Map.add (8<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 3<_>)

        |> Map.add (9<ParserStateIdentifier>, AugmentedTerminal.Terminal "(") (Action <| Reduce 4<_>)
        |> Map.add (9<ParserStateIdentifier>, AugmentedTerminal.Terminal ")") (Action <| Reduce 4<_>)
        |> Map.add (9<ParserStateIdentifier>, AugmentedTerminal.Terminal ",") (Action <| Reduce 4<_>)
        |> Map.add (9<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Reduce 4<_>)
        |> Map.add (9<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 4<_>)

    //
    let expectedGotoTable : Map<NonterminalTransition<AugmentedNonterminal<char>>, ParserStateId> =
        Map.empty
        |> Map.add (1<_>, AugmentedNonterminal.Nonterminal 'S') 4<_>
        |> Map.add (3<_>, AugmentedNonterminal.Nonterminal 'L') 6<_>
        |> Map.add (3<_>, AugmentedNonterminal.Nonterminal 'S') 5<_>
        |> Map.add (7<_>, AugmentedNonterminal.Nonterminal 'S') 9<_>

    // Verify the ACTION table.
    lr0ParserTable.ActionTable
    |> should equal expectedActionTable

    // Verify the GOTO table.
    lr0ParserTable.GotoTable
    |> should equal expectedGotoTable

[<TestCase>]
let ``LR(0) table for Grammar 3.23`` () =
    let lr0ParserTable = Lr0.createTable Appel.``Grammar 3.23``
    // table should have 6 states and 3 rules

    let expectedActionTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 3<_>)

        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.Terminal "+") (Conflict <| ShiftReduce (5<_>, 1<_>))
        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Reduce 1<_>)
        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 1<_>)

        |> Map.add (3<ParserStateIdentifier>, AugmentedTerminal.Terminal "+") (Action <| Reduce 2<_>)
        |> Map.add (3<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Reduce 2<_>)
        |> Map.add (3<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 2<_>)

        |> Map.add (4<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action Accept)

        |> Map.add (5<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 3<_>)

        |> Map.add (6<ParserStateIdentifier>, AugmentedTerminal.Terminal "+") (Action <| Reduce 3<_>)
        |> Map.add (6<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Reduce 3<_>)
        |> Map.add (6<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 3<_>)

    //
    let expectedGotoTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'E') 4<_>
        |> Map.add (1<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'T') 2<_>
        |> Map.add (5<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'E') 6<_>
        |> Map.add (5<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'T') 2<_>

    // Verify the ACTION table.
    lr0ParserTable.ActionTable
    |> should equal expectedActionTable

    // Verify the GOTO table.
    lr0ParserTable.GotoTable
    |> should equal expectedGotoTable

[<TestCase>]
let ``SLR table for Grammar 3.23`` () =
    let lr0ParserTable = Lr0.createTable Appel.``Grammar 3.23``

    let slr1ParserTable =
        let productionRuleIds = Grammar.ProductionRuleIds Appel.``Grammar 3.23``
        Slr1.upgrade (Appel.``Grammar 3.23``, lr0ParserTable, productionRuleIds)

    let expectedActionTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 3<_>)

        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.Terminal "+") (Action <| Shift 5<_>)
        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 1<_>)

        |> Map.add (3<ParserStateIdentifier>, AugmentedTerminal.Terminal "+") (Action <| Reduce 2<_>)
        |> Map.add (3<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 2<_>)

        |> Map.add (4<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action Accept)

        |> Map.add (5<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 3<_>)

        |> Map.add (6<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 3<_>)

    let expectedGotoTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'E') 4<_>
        |> Map.add (1<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'T') 2<_>
        |> Map.add (5<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'E') 6<_>
        |> Map.add (5<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'T') 2<_>

    // Verify the ACTION table.
    slr1ParserTable.ActionTable
    |> should equal expectedActionTable

    // Verify the GOTO table.
    slr1ParserTable.GotoTable
    |> should equal expectedGotoTable

[<TestCase>]
let ``LR(1) table for Grammar 3.26`` () =
    let parserTable = Lr1.createTable Appel.``Grammar 3.26``

    let expectedActionTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, AugmentedTerminal.Terminal "*") (Action <| Shift 5<_>)
        |> Map.add (1<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 4<_>)

        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.Terminal "=") (Action <| Shift 9<_>)
        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 1<_>)

        |> Map.add (3<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 2<_>)

        |> Map.add (4<ParserStateIdentifier>, AugmentedTerminal.Terminal "=") (Action <| Reduce 3<_>)
        |> Map.add (4<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 3<_>)

        |> Map.add (5<ParserStateIdentifier>, AugmentedTerminal.Terminal "*") (Action <| Shift 5<_>)
        |> Map.add (5<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 4<_>)

        |> Map.add (6<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action Accept)

        |> Map.add (7<ParserStateIdentifier>, AugmentedTerminal.Terminal "=") (Action <| Reduce 1<_>)
        |> Map.add (7<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 1<_>)

        |> Map.add (8<ParserStateIdentifier>, AugmentedTerminal.Terminal "=") (Action <| Reduce 4<_>)
        |> Map.add (8<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 4<_>)

        |> Map.add (9<ParserStateIdentifier>, AugmentedTerminal.Terminal "*") (Action <| Shift 13<_>)
        |> Map.add (9<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 12<_>)

        |> Map.add (10<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 1<_>)

        |> Map.add (11<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 5<_>)

        |> Map.add (12<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 3<_>)

        |> Map.add (13<ParserStateIdentifier>, AugmentedTerminal.Terminal "*") (Action <| Shift 13<_>)
        |> Map.add (13<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 12<_>)
        
        |> Map.add (14<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 4<_>)

    let expectedGotoTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'E') 3<_>
        |> Map.add (1<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'S') 6<_>
        |> Map.add (1<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'V') 2<_>

        |> Map.add (5<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'E') 8<_>
        |> Map.add (5<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'V') 7<_>

        |> Map.add (9<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'E') 11<_>
        |> Map.add (9<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'V') 10<_>

        |> Map.add (13<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'E') 14<_>
        |> Map.add (13<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'V') 10<_>

    // Verify the ACTION table.
    parserTable.ActionTable
    |> should equal expectedActionTable

    // Verify the GOTO table.
    parserTable.GotoTable
    |> should equal expectedGotoTable

[<TestCase>]
let ``LALR(1) table for Grammar 3.26`` () =
    let lr0ParserTable = Lr0.createTable Appel.``Grammar 3.26``

    let lalr1ParserTable =
        let productionRuleIds = Grammar.ProductionRuleIds Appel.``Grammar 3.26``
        match Lalr1.lookaheadSets (Appel.``Grammar 3.26``, lr0ParserTable) with
        | Choice2Of2 errMsg ->
            Assert.Fail errMsg
            // To satisfy F# type inference -- the test will actually fail on the Assert.Fail call.
            raise <| exn errMsg

        | Choice1Of2 lookaheadSets ->
            Lalr1.upgrade (Appel.``Grammar 3.26``, lr0ParserTable, productionRuleIds, lookaheadSets)

    let expectedActionTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, AugmentedTerminal.Terminal "*") (Action <| Shift 1<_>)
        |> Map.add (1<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 8<_>)

        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.Terminal "*") (Action <| Shift 1<_>)
        |> Map.add (2<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 8<_>)

        |> Map.add (3<ParserStateIdentifier>, AugmentedTerminal.Terminal "*") (Action <| Shift 1<_>)
        |> Map.add (3<ParserStateIdentifier>, AugmentedTerminal.Terminal "x") (Action <| Shift 8<_>)

        |> Map.add (4<ParserStateIdentifier>, AugmentedTerminal.Terminal "=") (Action <| Reduce 1<_>)
        |> Map.add (4<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 1<_>)

        |> Map.add (5<ParserStateIdentifier>, AugmentedTerminal.Terminal "=") (Action <| Shift 3<_>)
        |> Map.add (5<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 1<_>)

        |> Map.add (6<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 2<_>)

        |> Map.add (7<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 5<_>)

        |> Map.add (8<ParserStateIdentifier>, AugmentedTerminal.Terminal "=") (Action <| Reduce 3<_>)
        |> Map.add (8<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 3<_>)

        |> Map.add (9<ParserStateIdentifier>, AugmentedTerminal.Terminal "=") (Action <| Reduce 4<_>)
        |> Map.add (9<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action <| Reduce 4<_>)

        |> Map.add (10<ParserStateIdentifier>, AugmentedTerminal.EndOfFile) (Action Accept)

    let expectedGotoTable =
        Map.empty
        |> Map.add (1<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'E') 9<_>
        |> Map.add (1<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'V') 4<_>

        |> Map.add (2<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'E') 6<_>
        |> Map.add (2<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'S') 10<_>
        |> Map.add (2<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'V') 5<_>

        |> Map.add (3<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'E') 7<_>
        |> Map.add (3<ParserStateIdentifier>, AugmentedNonterminal.Nonterminal 'V') 4<_>

    // Verify the ACTION table.
    lalr1ParserTable.ActionTable
    |> should equal expectedActionTable

    // Verify the GOTO table.
    lalr1ParserTable.GotoTable
    |> should equal expectedGotoTable

