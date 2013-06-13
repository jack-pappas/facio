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
open ExtCore.Control
open ExtCore.Control.Collections
open Graham
open AugmentedPatterns
open Graham.Analysis
open Graham.Graph


/// Represents an empty lookahead.
/// This is an optimized representation used for the lookahead field
/// of an LR(0) item to minimize memory usage.
type EmptyLookahead = unit      // byte

/// An LR(0) item.
type Lr0Item<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrItem<'Nonterminal, 'Terminal, EmptyLookahead>

/// An LR(0) parser state -- i.e., a set of LR(0) items.
type Lr0ParserState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrParserState<'Nonterminal, 'Terminal, EmptyLookahead>

/// LR(0) parser table generation state.
type Lr0TableGenState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrTableGenState<'Nonterminal, 'Terminal, EmptyLookahead>

/// An LR(0) parser table.
type Lr0ParserTable<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrParserTable<'Nonterminal, 'Terminal, EmptyLookahead>

/// LR(0) parser tables.
[<RequireQualifiedAccess>]
module Lr0 =
    //
    [<RequireQualifiedAccess>]
    module private ParserState =
        //
        let isReduceState (parserState : Lr0ParserState<'Nonterminal, 'Terminal>)
            (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>) =
            // A parser state is a 'reduce state' if any of its items
            // have a parser position past the end of the production.
            parserState
            |> Set.exists (fun item ->
                let productionLength =
                    taggedGrammar.Productions
                    |> TagMap.find item.ProductionRuleIndex
                    |> Array.length
                int item.Position = productionLength)


    /// Functions for manipulating LR(0) parser items.
    [<RequireQualifiedAccess>]
    module private Item =
(*
        /// Determines if an LR(0) item is a 'kernel' item.
        let isKernelItem (item : Lr0Item<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>>) =
            // An LR(0) item is a kernel item iff it is the initial item or
            // the dot (representing the parser position) is NOT in the leftmost
            // (zeroth) position of the production.
            if item.Position > 0<_> then true
            else
                // Is this the initial item?
                match item.Nonterminal with
                | Start -> true
                | Nonterminal _ -> false
*)
        /// Computes the LR(0) closure of a set of items using a worklist-style algorithm.
        let rec private closureImpl (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>) items pendingItems : LrParserState<_,_,_> =
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
                        match LrItem.CurrentSymbol item taggedGrammar with
                        | None
                        | Some (Symbol.Terminal _) ->
                            items, pendingItems
                        | Some (Symbol.Nonterminal nonterminal) ->
                            // For all productions of this nonterminal, create a new item
                            // with the parser position at the beginning of the production.
                            // Add these new items into the set of items.
                            let pendingItems =
                                /// The productions of this nonterminal.
                                let nonterminalProductions = TagMap.find nonterminal taggedGrammar.ProductionsByNonterminal

                                (pendingItems, nonterminalProductions)
                                ||> TagSet.fold (fun pendingItems ruleIndex ->
                                    let newItem = LrItem (ruleIndex, GenericZero, ())

                                    // Only add this item to the worklist if it hasn't been seen yet.
                                    if Set.contains newItem items then pendingItems
                                    else newItem :: pendingItems)

                            // Return the updated item set and worklist.
                            items, pendingItems)

                // Recurse to continue processing.
                // OPTIMIZE : It's not really necessary to reverse the list here -- we could just as easily
                // process the list in reverse but for now we'll process it in order to make the algorithm
                // easier to understand/trace.
                closureImpl taggedGrammar items (List.rev pendingItems)

        /// Computes the LR(0) closure of a set of items.
        let closure (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>) items =
            // Call the recursive implementation, starting with the specified initial item set.
            closureImpl taggedGrammar Set.empty (Set.toList items)

        /// Moves the 'dot' (the current parser position) past the
        /// specified symbol for each item in a set of items.
        let goto symbol items (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>) : LrParserState<_,_,_> =
            (Set.empty, items)
            ||> Set.fold (fun updatedItems (item : LrItem<_,_,_>) ->
                // If the next symbol to be parsed in the production is the
                // specified symbol, create a new item with the position advanced
                // to the right of the symbol and add it to the updated items set.
                match LrItem.CurrentSymbol item taggedGrammar with
                | Some sym when sym = symbol ->
                    let updatedItem =
                        LrItem.NextPosition item
                    Set.add updatedItem updatedItems

                | _ ->
                    updatedItems)
            // Return the closure of the item set.
            |> closure taggedGrammar

    //
    let rec private createTableImpl (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>) eofIndex workSet =
        state {
        // If the work-set is empty, we're done creating the table.
        if TagSet.isEmpty workSet then
            return ()
        else
            let! workSet =
                (TagSet.empty, workSet)
                ||> State.TagSet.fold (fun workSet stateId ->
                    state {
                    /// The current table-generation state.
                    let! tableGenState = State.getState

                    /// The set of parser items for this state.
                    let stateItems = TagBimap.find stateId tableGenState.ParserStates

                    return!
                        (workSet, stateItems)
                        ||> State.Set.fold (fun workSet item ->
                            state {
                            // If the parser position is at the end of the production,
                            // add a 'reduce' action for every terminal (token) in the grammar.
                            match LrItem.CurrentSymbol item taggedGrammar with
                            | None ->
                                // Add a 'reduce' action to the ACTION table for each terminal (token) in the grammar.
                                (* TEMP : Change this to use State.TagBimap.iter instead of manually handling the state. *)

                                let! state = State.getState
                                do!
                                    (state, taggedGrammar.Terminals)
                                    ||> TagBimap.fold (fun state terminalIndex _ ->
                                        // state {
                                        let key = stateId, terminalIndex
                                        //do! LrTableGenState.reduce key item.ProductionRuleIndex
                                        LrTableGenState.reduce key item.ProductionRuleIndex state
                                        |> snd)
                                        //})
                                    |> State.setState

                                // Return the current workset.
                                return workSet

                            | Some symbol ->
                                // Add actions to the table based on the next symbol to be parsed.
                                match symbol with
                                | Symbol.Terminal terminalIndex ->
                                    if terminalIndex = eofIndex then
                                        // When the end-of-file symbol is the next to be parsed,
                                        // add an 'accept' action to the table to indicate the
                                        // input has been parsed successfully.
                                        do! LrTableGenState.accept stateId taggedGrammar

                                        // Return the current workset.
                                        return workSet
                                    else
                                        /// The state (set of items) transitioned into
                                        /// via the edge labeled with this symbol.
                                        let targetState = Item.goto symbol stateItems taggedGrammar

                                        /// The identifier of the target state.
                                        let! isNewState, targetStateId = LrTableGenState.stateId targetState

                                        // If this is a new state, add it to the list of states which need to be visited.
                                        let workSet =
                                            if isNewState then
                                                TagSet.add targetStateId workSet
                                            else workSet

                                        // The next symbol to be parsed is a terminal (token),
                                        // so add a 'shift' action to this entry of the table.
                                        do!
                                            let key = stateId, terminalIndex
                                            LrTableGenState.shift key targetStateId

                                        // Return the current workset.
                                        return workSet

                                | Symbol.Nonterminal nonterminalIndex ->
                                    /// The state (set of items) transitioned into
                                    /// via the edge labeled with this symbol.
                                    let targetState = Item.goto symbol stateItems taggedGrammar

                                    /// The identifier of the target state.
                                    let! isNewState, targetStateId = LrTableGenState.stateId targetState

                                    // If this is a new state, add it to the list of states which need to be visited.
                                    let workSet =
                                        if isNewState then
                                            TagSet.add targetStateId workSet
                                        else workSet

                                    // The next symbol to be parsed is a nonterminal,
                                    // so add a 'goto' action to this entry of the table.
                                    do!
                                        let key = stateId, nonterminalIndex
                                        LrTableGenState.goto key targetStateId

                                    // Return the current workset.
                                    return workSet
                                })})

            // Recurse with the updated table-generation state and work-set.
            return! createTableImpl taggedGrammar eofIndex workSet
        }

    /// Creates an LR(0) parser table from a tagged grammar.
    let createTable (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>)
        : Lr0ParserTable<'Nonterminal, 'Terminal> =
        // Preconditions
        // TODO

        let workflow =
            state {
            /// The identifier for the initial parser state.
            let! (_, initialParserStateId) =
                /// The initial LR state (set of items) passed to 'createTableImpl'.
                let initialParserState =
                    let startItems =
                        let startNonterminalIndex = TagBimap.findValue Start taggedGrammar.Nonterminals
                        TagMap.find startNonterminalIndex taggedGrammar.ProductionsByNonterminal
                    
                    (Set.empty, startItems)
                    ||> TagSet.fold (fun items ruleIndex ->
                        // Create an 'item', with the parser position at
                        // the beginning of the production.
                        let item : Lr0Item<_,_> = LrItem (ruleIndex, GenericZero, ())
                        Set.add item items)
                    |> Item.closure taggedGrammar

                LrTableGenState.stateId initialParserState

            /// The tagged-index of the end-of-file marker.
            let eofIndex = TagBimap.findValue EndOfFile taggedGrammar.Terminals

            return! createTableImpl taggedGrammar eofIndex (TagSet.singleton initialParserStateId)
            }

        // Execute the workflow to create the parser table.
        LrTableGenState.empty
        |> State.execute workflow

