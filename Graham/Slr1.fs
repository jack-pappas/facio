(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace Graham.LR

open LanguagePrimitives
open Graham.Grammar
open AugmentedPatterns
open Graham.Analysis
open Graham.Graph


/// <summary>SLR(1) parser table generator.</summary>
/// <remarks>Simple LR (SLR) is more powerful than LR(0), but less powerful
/// than either LR(1) or LALR(1). An SLR(1) parser table will have the same
/// number of parser states (table rows) as an LR(0) parser table for a
/// given grammar; the only difference is that SLR(1) uses the FOLLOW sets
/// of the grammar's nonterminals to resolve some conflicts automatically.</remarks>
[<RequireQualifiedAccess>]
module Slr1 =
    (*
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
        *)

    /// Given a grammar and it's LR(0) parser table, upgrades the table to SLR(1).
    let upgrade (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>, lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>) =
        /// Predictive sets of the augmented grammar.
        let predictiveSets = PredictiveSets.ofGrammar grammar

        // Upgrade the LR(0) parser table to SLR(1).
        // If the table has already been upgraded to SLR(1) (or something
        // more powerful, like LALR(1)), this has no effect.
        (lr0ParserTable, lr0ParserTable.ParserStates)
        ||> Map.fold (fun parserTable stateId items ->
            (parserTable, items)
            ||> Set.fold (fun parserTable item ->
                // If the parser position is at the end of this item's production,
                // remove the Reduce actions from the ACTION table for any tokens
                // which aren't in this nonterminal's FOLLOW set.
                if int item.Position = Array.length item.Production then
                    /// The rule nonterminal's FOLLOW set.
                    let nonterminalFollow =
                        Map.find item.Nonterminal predictiveSets.Follow

                    // Remove the unnecessary Reduce actions, thereby resolving some conflicts.
                    let actionTable =
                        let action =
                            parserTable.ReductionRulesById
                            // OPTIMIZE : This lookup is slow (O(n)) -- we should use a Bimap instead.
                            |> Map.pick (fun ruleId key ->
                                if key = (item.Nonterminal, item.Production) then
                                    Some ruleId
                                else None)
                            |> LrParserAction.Reduce
                        (parserTable.ActionTable, grammar.Terminals)
                        ||> Set.fold (fun actionTable terminal ->
                            // Is this terminal in the nonterminal's FOLLOW set?
                            if Set.contains terminal nonterminalFollow then
                                actionTable
                            else
                                //
                                let tableKey = stateId, terminal

                                // Don't need to do anything if there's no entry for this key;
                                // it may mean that the table has already been upgraded to SLR(1).
                                match Map.tryFind tableKey actionTable with
                                | None ->
                                    actionTable
                                | Some entry ->
                                    // Remove the Reduce action from the action set.
                                    let entry = Set.remove action entry

                                    // If the entry is now empty, remove it from the ACTION table;
                                    // otherwise, update the entry in the ACTION table.
                                    if Set.isEmpty entry then
                                        Map.remove tableKey actionTable
                                    else
                                        Map.add tableKey entry actionTable)

                    // Pass the modified parser table to the next iteration.
                    { parserTable with ActionTable = actionTable; }
                else
                    parserTable))


