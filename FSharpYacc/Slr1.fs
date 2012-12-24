(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace FSharpYacc.LR

open LanguagePrimitives
open FSharpYacc.Grammar
open AugmentedPatterns
open FSharpYacc.Analysis
open FSharpYacc.Graph


/// <summary>SLR(1) parser table generator.</summary>
/// <remarks>Simple LR (SLR) is more powerful than LR(0), but less powerful
/// than either LR(1) or LALR(1). An SLR(1) parser table will have the same
/// number of parser states (table rows) as an LR(0) parser table for a
/// given grammar; the only difference is that SLR(1) uses the FOLLOW sets
/// of the grammar's nonterminals to resolve some conflicts automatically.</remarks>
[<RequireQualifiedAccess>]
module internal Slr1 =
    (* TODO :   This code could be greatly simplified -- we could just construct the LR(0)
                parser table, then go back through it and remove any Reduce actions which
                would NOT have been added by SLR(1). This would also serve as a nice way to
                show how SLR(1) is like LR(0) but "upgraded" with a simple conflict-resolving strategy. *)

    //
    let rec private createTableImpl (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) predictiveSets (tableGenState : Lr0TableGenState<_,_>) : Lr0ParserTable<_,_> =
        // Preconditions
        assert (not <| Map.isEmpty tableGenState.ParserStateIds)

        let tableGenState' =
            (tableGenState, tableGenState.ParserStateIds)
            ||> Map.fold (fun tableGenState stateItems stateId ->
                (tableGenState, stateItems)
                ||> Set.fold (fun tableGenState item ->
                    // If the parser position is at the end of the production,
                    // add a 'reduce' action for every terminal (token) in the grammar.
                    if int item.Position = Array.length item.Production then
                        // First, add this reduction rule to the table-gen state,
                        // which gives us an identifier for the rule.
                        let reductionRuleId, tableGenState =
                            LrTableGenState.reductionRuleId (item.Nonterminal, item.Production) tableGenState

                        (*  Simple LR (SLR) parsers only differ from LR(0) parsers in one way:
                            instead of creating 'reduce' actions for all terminals (tokens)
                            in the grammar, we only create them for the tokens in the FOLLOW set
                            of this item's nonterminal. *)

                        let tokens = Map.find item.Nonterminal predictiveSets.Follow                            

                        // Add 'reduce' actions to the parser table.
                        Lr0.TableGenState.reduce stateId reductionRuleId tokens tableGenState
                        // TEMP : Discard the unit return value until we can use a monadic fold.
                        |> snd
                    else
                        // Add actions to the table based on the next symbol to be parsed.
                        match item.Production.[int item.Position] with
                        | Symbol.Terminal EndOfFile ->
                            // When the end-of-file symbol is the next to be parsed,
                            // add an 'accept' action to the table to indicate the
                            // input has been parsed successfully.
                            LrTableGenState.accept stateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Terminal (Terminal _ as token) as symbol ->                            
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Lr0.Item.goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                LrTableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a terminal (token),
                            // so add a 'shift' action to this entry of the table.
                            LrTableGenState.shift stateId token targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Nonterminal nonterm as symbol ->
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Lr0.Item.goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                LrTableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a nonterminal,
                            // so add a 'goto' action to this entry of the table.
                            LrTableGenState.goto stateId nonterm targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd
                        ))
            
        // If any states or transition-edges have been added, we need to recurse
        // and continue until we reach a fixpoint; otherwise, return the completed table.
        if tableGenState.ParserStateIds <> tableGenState'.ParserStateIds ||
            tableGenState.ActionTable <> tableGenState'.ActionTable ||
            tableGenState.GotoTable <> tableGenState'.GotoTable then
            createTableImpl grammar predictiveSets tableGenState'
        else
            // Create the parser table from the table-gen state.
            {   ParserStates =
                    (Map.empty, tableGenState.ParserStateIds)
                    ||> Map.fold (fun parserStates state stateId ->
                        Map.add stateId state parserStates);
                ParserTransitions = tableGenState.ParserTransitions;
                ActionTable = tableGenState.ActionTable;
                GotoTable = tableGenState.GotoTable;
                ReductionRulesById = tableGenState.ReductionRulesById; }

    /// Creates a Simple LR (SLR) parser table from the specified grammar.
    let createTable (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) =
        /// Predictive sets of the augmented grammar.
        let predictiveSets = PredictiveSets.ofGrammar grammar

        /// The initial state (set of items) passed to 'createTable'.
        let initialParserState =
            grammar.Productions
            |> Map.find Start
            |> Array.map (fun production ->
                // Create an 'item', with the parser position at
                // the beginning of the production.
                {   Nonterminal = Start;
                    Production = production;
                    Position = GenericZero;
                    Lookahead = (); })
            |> Set.ofArray
            |> Lr0.Item.closure grammar.Productions

        // The initial table-gen state.
        let initialParserStateId, initialTableGenState =
            LrTableGenState.stateId initialParserState LrTableGenState.empty

        // Create the parser table.
        createTableImpl grammar predictiveSets initialTableGenState


