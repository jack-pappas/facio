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

module Graham.Tests.Tables

open Grammars

open NUnit.Framework
open FsUnit

open Graham.Grammar
open Graham.Analysis
open Graham.LR


/// Helper functions for creating LR parser tables for tests.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private Table =
    /// Add a terminal entry to the action table.
    let term (parserStateId : int) (terminal : 'Terminal) action
        (table : Map<TerminalTransition<AugmentedTerminal<'Terminal>>, LrParserActionSet>) =
        /// The tagged parser state id.
        let parserState = LanguagePrimitives.Int32WithMeasure<ParserStateIdentifier> parserStateId

        table |> Map.add (parserState, AugmentedTerminal.Terminal terminal) action

    /// Add an EOF entry to the action table.
    let eof (parserStateId : int) action
        (table : Map<TerminalTransition<AugmentedTerminal<'Terminal>>, LrParserActionSet>) =
        /// The tagged parser state id.
        let parserState = LanguagePrimitives.Int32WithMeasure<ParserStateIdentifier> parserStateId

        table |> Map.add (parserState, AugmentedTerminal.EndOfFile) action

    /// Add an entry to the GOTO table.
    let nterm (sourceStateId : int) (nonterminal : 'Nonterminal) (targetStateId : int)
        (table : Map<NonterminalTransition<AugmentedNonterminal<'Nonterminal>>, ParserStateId>) =
        /// The tagged source state id.
        let sourceState = LanguagePrimitives.Int32WithMeasure<ParserStateIdentifier> sourceStateId
        /// The tagged target state id.
        let targetState = LanguagePrimitives.Int32WithMeasure<ParserStateIdentifier> targetStateId

        table |> Map.add (sourceState, AugmentedNonterminal.Nonterminal nonterminal) targetState


[<TestCase>]
let ``LR(0) table for Grammar 3.20`` () =    
    let expectedActionTable =
        Map.empty
        |> Table.term 0 "(" (Action <| Shift 3<_>)
        |> Table.term 0 "x" (Action <| Shift 2<_>)

        |> Table.eof 1 (Action Accept)

        |> Table.term 2 "(" (Action <| Reduce 4<_>)
        |> Table.term 2 ")" (Action <| Reduce 4<_>)
        |> Table.term 2 "," (Action <| Reduce 4<_>)
        |> Table.term 2 "x" (Action <| Reduce 4<_>)
        |> Table.eof 2 (Action <| Reduce 4<_>)

        |> Table.term 3 "(" (Action <| Shift 3<_>)
        |> Table.term 3 "x" (Action <| Shift 2<_>)

        |> Table.term 4 "(" (Action <| Reduce 1<_>)
        |> Table.term 4 ")" (Action <| Reduce 1<_>)
        |> Table.term 4 "," (Action <| Reduce 1<_>)
        |> Table.term 4 "x" (Action <| Reduce 1<_>)
        |> Table.eof 4 (Action <| Reduce 1<_>)

        |> Table.term 5 ")" (Action <| Shift 7<_>)
        |> Table.term 5 "," (Action <| Shift 6<_>)

        |> Table.term 6 "(" (Action <| Shift 3<_>)
        |> Table.term 6 "x" (Action <| Shift 2<_>)

        |> Table.term 7 "(" (Action <| Reduce 3<_>)
        |> Table.term 7 ")" (Action <| Reduce 3<_>)
        |> Table.term 7 "," (Action <| Reduce 3<_>)
        |> Table.term 7 "x" (Action <| Reduce 3<_>)
        |> Table.eof 7 (Action <| Reduce 3<_>)

        |> Table.term 8 "(" (Action <| Reduce 2<_>)
        |> Table.term 8 ")" (Action <| Reduce 2<_>)
        |> Table.term 8 "," (Action <| Reduce 2<_>)
        |> Table.term 8 "x" (Action <| Reduce 2<_>)
        |> Table.eof 8 (Action <| Reduce 2<_>)

    //
    let expectedGotoTable =
        Map.empty
        |> Table.nterm 0 'S' 1
        |> Table.nterm 3 'S' 4
        |> Table.nterm 3 'L' 5
        |> Table.nterm 6 'S' 8

    let lr0ParserTable = Lr0.createTable Appel.``Grammar 3.20``

    // Verify the ACTION table.
    lr0ParserTable.ActionTable
    |> should equal expectedActionTable

    // Verify the GOTO table.
    lr0ParserTable.GotoTable
    |> should equal expectedGotoTable

[<TestCase>]
let ``LR(0) table for Grammar 3.23`` () =
    let expectedActionTable =
        Map.empty
        |> Table.term 1 "x" (Action <| Shift 3<_>)

        |> Table.term 2 "+" (Conflict <| ShiftReduce (5<_>, 1<_>))
        |> Table.term 2 "x" (Action <| Reduce 1<_>)
        |> Table.eof 2 (Action <| Reduce 1<_>)

        |> Table.term 3 "+" (Action <| Reduce 2<_>)
        |> Table.term 3 "x" (Action <| Reduce 2<_>)
        |> Table.eof 3 (Action <| Reduce 2<_>)

        |> Table.eof 4 (Action Accept)

        |> Table.term 5 "x" (Action <| Shift 3<_>)

        |> Table.term 6 "+" (Action <| Reduce 3<_>)
        |> Table.term 6 "x" (Action <| Reduce 3<_>)
        |> Table.eof 6 (Action <| Reduce 3<_>)

    //
    let expectedGotoTable =
        Map.empty
        |> Table.nterm 1 'E' 4
        |> Table.nterm 1 'T' 2
        |> Table.nterm 5 'E' 6
        |> Table.nterm 5 'T' 2

    let lr0ParserTable = Lr0.createTable Appel.``Grammar 3.23``
    // table should have 6 states and 3 rules

    // Verify the ACTION table.
    lr0ParserTable.ActionTable
    |> should equal expectedActionTable

    // Verify the GOTO table.
    lr0ParserTable.GotoTable
    |> should equal expectedGotoTable

[<TestCase>]
let ``SLR table for Grammar 3.23`` () =
    let expectedActionTable =
        Map.empty
        |> Table.term 1 "x" (Action <| Shift 3<_>)

        |> Table.term 2 "+" (Action <| Shift 5<_>)
        |> Table.eof 2 (Action <| Reduce 1<_>)

        |> Table.term 3 "+" (Action <| Reduce 2<_>)
        |> Table.eof 3 (Action <| Reduce 2<_>)

        |> Table.eof 4 (Action Accept)

        |> Table.term 5 "x" (Action <| Shift 3<_>)

        |> Table.eof 6 (Action <| Reduce 3<_>)

    let expectedGotoTable =
        Map.empty
        |> Table.nterm 1 'E' 4
        |> Table.nterm 1 'T' 2
        |> Table.nterm 5 'E' 6
        |> Table.nterm 5 'T' 2

    let lr0ParserTable = Lr0.createTable Appel.``Grammar 3.23``

    let slr1ParserTable =
        let productionRuleIds = Grammar.ProductionRuleIds Appel.``Grammar 3.23``
        Slr1.upgrade (Appel.``Grammar 3.23``, lr0ParserTable, productionRuleIds)

    // Verify the ACTION table.
    slr1ParserTable.ActionTable
    |> should equal expectedActionTable

    // Verify the GOTO table.
    slr1ParserTable.GotoTable
    |> should equal expectedGotoTable

[<TestCase>]
let ``LR(1) table for Grammar 3.26`` () =
    let expectedActionTable =
        Map.empty
        |> Table.term 1 "*" (Action <| Shift 5<_>)
        |> Table.term 1 "x" (Action <| Shift 4<_>)

        |> Table.term 2 "=" (Action <| Shift 9<_>)
        |> Table.eof 2 (Action <| Reduce 1<_>)

        |> Table.eof 3 (Action <| Reduce 2<_>)

        |> Table.term 4 "=" (Action <| Reduce 3<_>)
        |> Table.eof 4 (Action <| Reduce 3<_>)

        |> Table.term 5 "*" (Action <| Shift 5<_>)
        |> Table.term 5 "x" (Action <| Shift 4<_>)

        |> Table.eof 6 (Action Accept)

        |> Table.term 7 "=" (Action <| Reduce 1<_>)
        |> Table.eof 7 (Action <| Reduce 1<_>)

        |> Table.term 8 "=" (Action <| Reduce 4<_>)
        |> Table.eof 8 (Action <| Reduce 4<_>)

        |> Table.term 9 "*" (Action <| Shift 13<_>)
        |> Table.term 9 "x" (Action <| Shift 12<_>)

        |> Table.eof 10 (Action <| Reduce 1<_>)

        |> Table.eof 11 (Action <| Reduce 5<_>)

        |> Table.eof 12 (Action <| Reduce 3<_>)

        |> Table.term 13 "*" (Action <| Shift 13<_>)
        |> Table.term 13 "x" (Action <| Shift 12<_>)
        
        |> Table.eof 14 (Action <| Reduce 4<_>)

    let expectedGotoTable =
        Map.empty
        |> Table.nterm 1 'E' 3
        |> Table.nterm 1 'S' 6
        |> Table.nterm 1 'V' 2
        
        |> Table.nterm 5 'E' 8
        |> Table.nterm 5 'V' 7
        
        |> Table.nterm 9 'E' 11
        |> Table.nterm 9 'V' 10

        |> Table.nterm 13 'E' 14
        |> Table.nterm 13 'V' 10

    let parserTable = Lr1.createTable Appel.``Grammar 3.26``

    // Verify the ACTION table.
    parserTable.ActionTable
    |> should equal expectedActionTable

    // Verify the GOTO table.
    parserTable.GotoTable
    |> should equal expectedGotoTable

[<TestCase>]
let ``LALR(1) table for Grammar 3.26`` () =
    let expectedActionTable =
        Map.empty
        |> Table.term 1 "*" (Action <| Shift 1<_>)
        |> Table.term 1 "x" (Action <| Shift 8<_>)

        |> Table.term 2 "*" (Action <| Shift 1<_>)
        |> Table.term 2 "x" (Action <| Shift 8<_>)

        |> Table.term 3 "*" (Action <| Shift 1<_>)
        |> Table.term 3 "x" (Action <| Shift 8<_>)

        |> Table.term 4 "=" (Action <| Reduce 1<_>)
        |> Table.eof 4 (Action <| Reduce 1<_>)

        |> Table.term 5 "=" (Action <| Shift 3<_>)
        |> Table.eof 5 (Action <| Reduce 1<_>)

        |> Table.eof 6 (Action <| Reduce 2<_>)

        |> Table.eof 7 (Action <| Reduce 5<_>)

        |> Table.term 8 "=" (Action <| Reduce 3<_>)
        |> Table.eof 8 (Action <| Reduce 3<_>)

        |> Table.term 9 "=" (Action <| Reduce 4<_>)
        |> Table.eof 9 (Action <| Reduce 4<_>)

        |> Table.eof 10 (Action Accept)

    let expectedGotoTable =
        Map.empty
        |> Table.nterm 1 'E' 9
        |> Table.nterm 1 'V' 4

        |> Table.nterm 2 'E' 6
        |> Table.nterm 2 'S' 10
        |> Table.nterm 2 'V' 5

        |> Table.nterm 3 'E' 7
        |> Table.nterm 3 'V' 4

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

    // Verify the ACTION table.
    lalr1ParserTable.ActionTable
    |> should equal expectedActionTable

    // Verify the GOTO table.
    lalr1ParserTable.GotoTable
    |> should equal expectedGotoTable

