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

namespace Graham.LR

open LanguagePrimitives
open ExtCore
open ExtCore.Collections
open ExtCore.Control
open ExtCore.Control.Collections
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

        //
        let rec private closureImpl (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) predictiveSets items pendingItems : LrParserState<_,_,_> =
            match pendingItems with
            | [] ->
                items
            | _ ->
                // Process the worklist.
                let items, pendingItems =
                    ((items, []), pendingItems)
                    ||> List.fold (fun (items, pendingItems) (item : LrItem<_,_,_>) ->
                        // Add the current item to the item set.
                        let items = Set.add item items

                        // If the position is at the end of the production, or if the current symbol
                        // is a terminal, there's nothing that needs to be done for this item.
                        match item.CurrentSymbol with
                        | None
                        | Some (Symbol.Terminal _) ->
                            items, pendingItems
                        | Some (Symbol.Nonterminal nontermId) ->
                            // For all productions of this nonterminal, create a new item
                            // with the parser position at the beginning of the production.
                            // Add these new items into the set of items.
                            let pendingItems =
                                /// The productions of this nonterminal.
                                let nontermProductions = Map.find nontermId productions

                                /// The FIRST set of the remaining symbols in this production
                                /// (i.e., the symbols following this nonterminal symbol),
                                /// plus the lookahead token from the item.
                                let firstSetOfRemainingSymbols =
                                    firstSetOfString item.Production (int item.Position + 1) item.Lookahead predictiveSets

                                // For all productions of this nonterminal, create a new item
                                // with the parser position at the beginning of the production.
                                // Add these new items into the set of items.
                                (pendingItems, nontermProductions)
                                ||> Array.fold (fun pendingItems production ->
                                    // Combine the production with each token which could
                                    // possibly follow this nonterminal.
                                    (pendingItems, firstSetOfRemainingSymbols)
                                    ||> Set.fold (fun pendingItems nontermFollowToken ->
                                        let newItem = {
                                            Nonterminal = nontermId;
                                            Production = production;
                                            Position = GenericZero;
                                            Lookahead = nontermFollowToken; }

                                        // Only add this item to the worklist if it hasn't been seen yet.
                                        if Set.contains newItem items then pendingItems
                                        else newItem :: pendingItems))

                            // Return the updated item set and worklist.
                            items, pendingItems)

                // Recurse to continue processing.
                // OPTIMIZE : It's not really necessary to reverse the list here -- we could just as easily
                // process the list in reverse but for now we'll process it in order to make the algorithm
                // easier to understand/trace.
                closureImpl productions predictiveSets items (List.rev pendingItems)

        /// Computes the LR(1) closure of a set of items.
        let closure (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) predictiveSets items : LrParserState<_,_,_> =
            // Call the recursive implementation, starting with the specified initial item set.
            closureImpl productions predictiveSets Set.empty (Set.toList items)

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
            closure grammar.Productions predictiveSets items


    //
    let rec private createTableImpl (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>, predictiveSets) workSet =
        readerState {
        // If the work-set is empty, we're finished creating the table.
        if TagSet.isEmpty workSet then
            return ()
        else
            let! workSet =
                (TagSet.empty, workSet)
                ||> ReaderState.TagSet.fold (fun workSet stateId ->
                    readerState {
                    /// The current table-generation state.
                    let! tableGenState = ReaderState.getState

                    /// The set of parser items for this state.
                    let stateItems = TagBimap.find stateId tableGenState.ParserStates

                    return!
                        (workSet, stateItems)
                        ||> ReaderState.Set.fold (fun workSet item ->
                            readerState {
                            // If the parser position is at the end of the production,
                            // add a 'reduce' action for every terminal (token) in the grammar.
                            match item.CurrentSymbol with
                            | None ->
                                /// The table-generation environment.
                                let! env = ReaderState.read

                                /// The production rule identifier for this production.
                                let productionRuleId =
                                    // Get the production-rule-id from the 'environment' component of the table-generation state.
                                    let productionKey = (item.Nonterminal, item.Production)
                                    Map.find productionKey env.ProductionRuleIds

                                // Add a 'reduce' action for the entry with this state and lookahead token.
                                do!
                                    let key = stateId, item.Lookahead
                                    LrTableGenState.reduce key productionRuleId
                                    |> ReaderState.liftState

                                // Return the current workset.
                                return workSet
                        
                            | Some symbol ->
                                // Add actions to the table based on the next symbol to be parsed.
                                match symbol with
                                | Symbol.Terminal EndOfFile ->
                                    // When the end-of-file symbol is the next to be parsed,
                                    // add an 'accept' action to the table to indicate the
                                    // input has been parsed successfully.
                                    do! LrTableGenState.accept stateId
                                        |> ReaderState.liftState

                                    // Return the current workset.
                                    return workSet

                                | Symbol.Terminal (Terminal _ as token) ->
                                    /// The state (set of items) transitioned into
                                    /// via the edge labeled with this symbol.
                                    let targetState = Item.goto symbol stateItems grammar predictiveSets

                                    /// The identifier of the target state.
                                    let! isNewState, targetStateId =
                                        LrTableGenState.stateId targetState
                                        |> ReaderState.liftState

                                    // If this is a new state, add it to the list of states which need to be visited.
                                    let workSet =
                                        if isNewState then
                                            TagSet.add targetStateId workSet
                                        else workSet

                                    // The next symbol to be parsed is a terminal (token),
                                    // so add a 'shift' action to this entry of the table.
                                    do!
                                        let key = stateId, token
                                        LrTableGenState.shift key targetStateId
                                        |> ReaderState.liftState

                                    // Return the current workset.
                                    return workSet

                                | Symbol.Nonterminal nonterm ->
                                    /// The state (set of items) transitioned into
                                    /// via the edge labeled with this symbol.
                                    let targetState = Item.goto symbol stateItems grammar predictiveSets

                                    /// The identifier of the target state.
                                    let! isNewState, targetStateId =
                                        LrTableGenState.stateId targetState
                                        |> ReaderState.liftState

                                    // If this is a new state, add it to the list of states which need to be visited.
                                    let workSet =
                                        if isNewState then
                                            TagSet.add targetStateId workSet
                                        else workSet

                                    // The next symbol to be parsed is a nonterminal,
                                    // so add a 'goto' action to this entry of the table.
                                    do!
                                        let key = stateId, nonterm
                                        LrTableGenState.goto key targetStateId
                                        |> ReaderState.liftState

                                    // Return the current workset.
                                    return workSet
                                })})

            // Recurse with the updated table-generation state and work-set.
            return! createTableImpl (grammar, predictiveSets) workSet
        }

    /// Create an LR(1) parser table for the specified grammar.
    let createTable (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>)
        : Lr1ParserTable<'Nonterminal, 'Terminal> =
        // Preconditions
        // TODO

        /// Analysis of the augmented grammar.
        let predictiveSets = PredictiveSets.ofGrammar grammar

        /// The parser table generation environment.
        let tableGenEnv = LrTableGenEnvironment.Create grammar.Productions

        let workflow =
            readerState {
            /// The identifier for the initial parser state.
            let! (_, initialParserStateId) =
                /// The initial LR state (set of items) passed to 'createTableImpl'.
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
                    |> Item.closure grammar.Productions predictiveSets

                ReaderState.liftState (LrTableGenState.stateId initialParserState)

            return! createTableImpl (grammar, predictiveSets) (TagSet.singleton initialParserStateId)
            }

        // Execute the workflow to create the parser table.
        (tableGenEnv, LrTableGenState.empty)
        ||> ReaderState.execute workflow

