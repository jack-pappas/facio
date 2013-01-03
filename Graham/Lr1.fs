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


/// An LR(1) item.
type Lr1Item<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrItem<'Nonterminal, 'Terminal, 'Terminal>

/// An LR(1) parser state -- i.e., a set of LR(1) items.
type Lr1ParserState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrParserState<'Nonterminal, 'Terminal, 'Terminal>

/// LR(1) parser table generation state.
type Lr1TableGenState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrTableGenState<'Nonterminal, 'Terminal, 'Terminal>

/// An LR(1) parser table.
type Lr1ParserTable<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrParserTable<
        AugmentedNonterminal<'Nonterminal>,
        AugmentedTerminal<'Terminal>,
        AugmentedTerminal<'Terminal>>

/// LR(1) parser tables.
[<RequireQualifiedAccess>]
module Lr1 =
    /// Functions for manipulating LR(1) parser items.
    [<RequireQualifiedAccess>]
    module Item =
        /// Computes the FIRST set of a string of symbols.
        /// The string is a "substring" of a production, followed by a lookahead token.
        let firstSetOfString (production : Symbol<'Nonterminal, 'Terminal>[]) startIndex lookahead predictiveSets =
            // Preconditions
            if startIndex < 0 then
                invalidArg "startIndex" "The start index cannot be negative."
            elif startIndex > Array.length production then
                invalidArg "startIndex" "The start index cannot be greater than the length of the production."

            let productionLength = Array.length production

            //
            let rec firstSetOfString firstSet symbolIndex =
                // If we've reached the end of the production,
                // add the lookahead token to the set and return.
                if symbolIndex = productionLength then
                    Set.add lookahead firstSet
                else
                    // Match on the current symbol of the production.
                    match production.[symbolIndex] with
                    | Symbol.Terminal token ->
                        // Add the token to the set; then, return
                        // because tokens are never nullable.
                        Set.add token firstSet

                    | Symbol.Nonterminal nontermId ->
                        /// The FIRST set of this nonterminal symbol.
                        let nontermFirstSet = Map.find nontermId predictiveSets.First

                        // Merge the FIRST set of this nonterminal symbol into
                        // the FIRST set of the string.
                        let firstSet = Set.union firstSet nontermFirstSet

                        // If this symbol is nullable, continue processing with
                        // the next symbol in the production; otherwise, return.
                        if Map.find nontermId predictiveSets.Nullable then
                            firstSetOfString firstSet (symbolIndex + 1)
                        else
                            firstSet

            // Call the recursive implementation to compute the FIRST set.
            firstSetOfString Set.empty startIndex

        /// Computes the LR(1) closure of a set of items.
        // TODO : Modify this to use a worklist-style algorithm to avoid
        // reprocessing items which already exist in the set (i.e., when iterating,
        // we only process items added to the set in the previous iteration).
        let closure (grammar : Grammar<'Nonterminal, 'Terminal>) predictiveSets items =
            /// Implementation of the LR(1) closure algorithm.
            let rec closure items =
                let items' =
                    (items, items)
                    ||> Set.fold (fun items item ->
                        // If the position is at the end of the production,
                        // there's nothing that needs to be done for this item.
                        if int item.Position = Array.length item.Production then
                            items
                        else
                            // Determine what to do based on the next symbol to be parsed.
                            match item.Production.[int item.Position] with
                            | Symbol.Terminal _ ->
                                // Nothing to do for terminals
                                items
                            | Symbol.Nonterminal nontermId ->
                                /// The productions of this nonterminal.
                                let nontermProductions = Map.find nontermId grammar.Productions
                            
                                /// The FIRST set of the remaining symbols in this production
                                /// (i.e., the symbols following this nonterminal symbol),
                                /// plus the lookahead token from the item.
                                let firstSetOfRemainingSymbols =
                                    firstSetOfString item.Production (int item.Position + 1) item.Lookahead predictiveSets

                                // For all productions of this nonterminal, create a new item
                                // with the parser position at the beginning of the production.
                                // Add these new items into the set of items.
                                (items, nontermProductions)
                                ||> Array.fold (fun items production ->
                                    // Combine the production with each token which could
                                    // possibly follow this nonterminal.
                                    (items, firstSetOfRemainingSymbols)
                                    ||> Set.fold (fun items nontermFollowToken ->
                                        let newItem = {
                                            Nonterminal = nontermId;
                                            Production = production;
                                            Position = GenericZero;
                                            Lookahead = nontermFollowToken; }

                                        Set.add newItem items)))

                // If the items set has changed, recurse for another iteration.
                // If not, we're done processing and the set is returned.
                if items' = items then
                    items
                else
                    closure items'

            // Compute the closure, starting with the specified initial item.
            closure items

        /// Moves the 'dot' (the current parser position) past the
        /// specified symbol for each item in a set of items.
        let goto symbol items (grammar : Grammar<'Nonterminal, 'Terminal>) predictiveSets =
            /// The updated 'items' set.
            let items =
                (Set.empty, items)
                ||> Set.fold (fun updatedItems item ->
                    // If the position is at the end of the production, we know
                    // this item can't be a match, so continue to to the next item.
                    if int item.Position = Array.length item.Production then
                        updatedItems
                    else
                        // If the next symbol to be parsed in the production is the
                        // specified symbol, create a new item with the position advanced
                        // to the right of the symbol and add it to the updated items set.
                        if item.Production.[int item.Position] = symbol then
                            let updatedItem =
                                { item with
                                    Position = item.Position + 1<_>; }
                            Set.add updatedItem updatedItems
                        else
                            // The symbol did not match, so this item won't be added to
                            // the updated items set.
                            updatedItems)

            // Return the closure of the item set.
            closure grammar predictiveSets items

    /// Functions which use the State monad to manipulate an LR(1) table-generation state.
    [<RequireQualifiedAccess>]
    module TableGenState =
        /// Add a 'reduce' action to the parser table for the specified lookahead token.
        let reduce (sourceState : ParserStateId)
                    (reductionRuleId : ReductionRuleId)
                    (lookaheadToken : AugmentedTerminal<'Terminal>)
                    (tableGenState : Lr1TableGenState<'Nonterminal, AugmentedTerminal<'Terminal>>) =
            //
            let tableKey = sourceState, lookaheadToken

            //
            let actionSet =
                match Map.tryFind tableKey tableGenState.ActionTable with
                | None ->
                    Action <| Reduce reductionRuleId
                | Some actionSet ->
                    match actionSet with
                    | Action (Shift shiftStateId) ->
                        Conflict <| ShiftReduce (shiftStateId, reductionRuleId)

                    | Action (Reduce reductionRuleId')
                    | Conflict (ShiftReduce (_, reductionRuleId'))
                    | Conflict (ReduceReduce (reductionRuleId', _))
                    | Conflict (ReduceReduce (_, reductionRuleId'))
                        when reductionRuleId = reductionRuleId' ->
                        // Return the existing action set without modifying it.
                        actionSet

                    | actionSet ->
                        // Adding this action to the existing action set would create
                        // an impossible set of actions, so raise an exception.
                        LrTableGenState.impossibleActionSetErrorMsg (
                            sourceState, lookaheadToken, actionSet, Reduce reductionRuleId)
                        |> invalidOp

            // Update the table with the new action set.
            (),
            { tableGenState with
                ActionTable = Map.add tableKey actionSet tableGenState.ActionTable; }


    //
    let rec private createTableImpl (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) predictiveSets (tableGenState : Lr1TableGenState<_,_>) =
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

                        // Add a 'reduce' action for the entry with this state and lookahead token.
                        TableGenState.reduce stateId reductionRuleId item.Lookahead tableGenState
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
                            let targetState = Item.goto symbol stateItems grammar predictiveSets

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
                            let targetState = Item.goto symbol stateItems grammar predictiveSets

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
            // Return the table-gen state itself -- the consuming method
            // can construct the table from it.
            tableGenState

    //
    let internal createTableGenState (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) =
        /// Analysis of the augmented grammar.
        let predictiveSets = PredictiveSets.ofGrammar grammar

        /// The initial state (set of items) passed to 'createTable'.
        let initialParserState : Lr1ParserState<_,_> =
            let startProductions = Map.find Start grammar.Productions
            (Set.empty, startProductions)
            ||> Array.fold (fun items production ->
                // Create an 'item', with the parser position at
                // the beginning of the production.
                let item = {
                    Nonterminal = Start;
                    Production = production;
                    Position = GenericZero;
                    // Any token can be used here, because the end-of-file symbol
                    // (in the augmented start production) will never be shifted.
                    // We use the EndOfFile token itself here to keep the code generic.
                    Lookahead = EndOfFile; }
                Set.add item items)
            |> Item.closure grammar predictiveSets

        // The initial table-gen state.
        let initialParserStateId, initialTableGenState =
            LrTableGenState.stateId initialParserState LrTableGenState.empty

        // Create the table-gen state.
        createTableImpl grammar predictiveSets initialTableGenState

    /// Create an LR(1) parser table for the specified grammar.
    let createTable (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) : Lr1ParserTable<'Nonterminal, 'Terminal> =
        // Create the table-gen state.
        let tableGenState = createTableGenState grammar

        // Create the LR(1) parser table from the table-gen state.
        {   ParserStates =
                (Map.empty, tableGenState.ParserStateIds)
                ||> Map.fold (fun parserStates state stateId ->
                    Map.add stateId state parserStates);
            ParserTransitions = tableGenState.ParserTransitions;
            ActionTable = tableGenState.ActionTable;
            GotoTable = tableGenState.GotoTable;
            ReductionRulesById = tableGenState.ReductionRulesById; }

