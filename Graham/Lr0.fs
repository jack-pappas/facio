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


/// An LR(0) item.
type Lr0Item<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrItem<'Nonterminal, 'Terminal, unit>

/// An LR(0) parser state -- i.e., a set of LR(0) items.
type Lr0ParserState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrParserState<'Nonterminal, 'Terminal, unit>

/// LR(0) parser table generation state.
type Lr0TableGenState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrTableGenState<'Nonterminal, 'Terminal, unit>

/// An LR(0) parser table.
type Lr0ParserTable<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrParserTable<
        AugmentedNonterminal<'Nonterminal>,
        AugmentedTerminal<'Terminal>,
        unit>

/// LR(0) parser tables.
[<RequireQualifiedAccess>]
module Lr0 =
    //
    [<RequireQualifiedAccess>]
    module private ParserState =
        //
        let isReduceState (parserState : Lr0ParserState<'Nonterminal, 'Terminal>) =
            // A parser state is a 'reduce state' if any of its items
            // have a parser position past the end of the production.
            parserState
            |> Set.exists (fun item ->
                int item.Position = Array.length item.Production)


    /// Functions for manipulating LR(0) parser items.
    [<RequireQualifiedAccess>]
    module private Item =
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

        /// Computes the LR(0) closure of a set of items using a worklist-style algorithm.
        let rec private closureImpl (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) items pendingItems : LrParserState<_,_,_> =
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

                        // If the position is at the end of the production,
                        // there's nothing that needs to be done for this item.
                        match item.CurrentSymbol with
                        | None ->
                            items, pendingItems
                        | Some sym ->
                            // Determine what to do based on the next symbol to be parsed.
                            match sym with
                            | Symbol.Terminal _ ->
                                // Nothing to do for terminals
                                items, pendingItems
                            | Symbol.Nonterminal nontermId ->
                                /// The productions of this nonterminal.
                                let nontermProductions = Map.find nontermId productions

                                // For all productions of this nonterminal, create a new item
                                // with the parser position at the beginning of the production.
                                // Add these new items into the set of items.
                                let pendingItems =
                                    (pendingItems, nontermProductions)
                                    ||> Array.fold (fun pendingItems production ->
                                        let newItem = {
                                            Nonterminal = nontermId;
                                            Production = production;
                                            Position = GenericZero;
                                            Lookahead = (); }

                                        // Only add this item to the worklist if it hasn't been seen yet.
                                        if Set.contains newItem items then pendingItems
                                        else newItem :: pendingItems)

                                // Return the updated item set and worklist.
                                items, pendingItems)

                // Recurse to continue processing.
                // OPTIMIZE : It's not really necessary to reverse the list here -- we could just as easily
                // process the list in reverse but for now we'll process it in order to make the algorithm
                // easier to understand/trace.
                closureImpl productions items (List.rev pendingItems)

        /// Computes the LR(0) closure of a set of items.
        let closure (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) items =
            // Call the recursive implementation, starting with the specified initial item set.
            closureImpl productions Set.empty (Set.toList items)

        /// Moves the 'dot' (the current parser position) past the
        /// specified symbol for each item in a set of items.
        let goto symbol items (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) : LrParserState<_,_,_> =
            (Set.empty, items)
            ||> Set.fold (fun updatedItems (item : LrItem<_,_,_>) ->
                // If the next symbol to be parsed in the production is the
                // specified symbol, create a new item with the position advanced
                // to the right of the symbol and add it to the updated items set.
                match item.CurrentSymbol with
                | Some sym when sym = symbol ->
                    let updatedItem =
                        { item with
                            Position = item.Position + 1<_>; }
                    Set.add updatedItem updatedItems

                | _ ->
                    updatedItems)
            // Return the closure of the item set.
            |> closure productions

    //
    let rec private createTableImpl (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) workSet =
        readerState {
        // If the work-set is empty, we're done creating the table.
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

                                // Add a 'reduce' action to the ACTION table for each terminal (token) in the grammar.
                                do! grammar.Terminals
                                    |> State.Set.iter (fun terminal ->
                                        state {
                                        let key = stateId, terminal
                                        do! LrTableGenState.reduce key productionRuleId
                                        })
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
                                    let targetState = Item.goto symbol stateItems grammar.Productions

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
                                    let targetState = Item.goto symbol stateItems grammar.Productions

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
            return! createTableImpl grammar workSet
        }

    /// Creates an LR(0) parser table from the specified grammar.
    let createTable (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>)
        : Lr0ParserTable<'Nonterminal, 'Terminal> =
        // Preconditions
        // TODO

        /// The parser table generation environment.
        let tableGenEnv = LrTableGenEnvironment.Create grammar.Productions

        let workflow =
            readerState {
            /// The identifier for the initial parser state.
            let! (_, initialParserStateId) =
                /// The initial LR state (set of items) passed to 'createTableImpl'.
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
                    |> Item.closure grammar.Productions

                ReaderState.liftState (LrTableGenState.stateId initialParserState)

            return! createTableImpl grammar (TagSet.singleton initialParserStateId)
            }

        // Execute the workflow to create the parser table.
        (tableGenEnv, LrTableGenState.empty)
        ||> ReaderState.execute workflow

    //
    let applyPrecedence (lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>,
                         settings : PrecedenceSettings<'Terminal>) : Lr0ParserTable<'Nonterminal, 'Terminal> =
        // Fold over the provided table, using the supplied precedence and
        // associativity tables to resolve conflicts wherever possible.
        (lr0ParserTable, lr0ParserTable.ActionTable)
        ||> Map.fold (fun lr0ParserTable ((_, terminal) as key) actionSet ->
            // Does this state contain a conflict?
            match actionSet with
            | Action _ ->
                lr0ParserTable
            | Conflict conflict ->
                //
                let terminal =
                    // The end-of-file marker is never shifted, so it can't possibly cause a conflict.
                    match terminal with
                    | EndOfFile ->
                        // TODO : Create a better error message here.
                        failwith "Found a conflict involving the end-of-file marker."
                    | Terminal terminal ->
                        terminal

                // Use the precedence and associativity tables to resolve this conflict (if possible).
                // If the conflict can be resolved, use the LrParserTable.RemoveAction method
                // to remove the action(s) we're not using.
                match conflict.Shift with
                | None ->
                    (*  Reduce-reduce conflicts aren't solved with precedence/associativity --
                        instead, they must be resolved by the 'resolveConflicts' function. *)
                    lr0ParserTable

                | Some targetStateId ->
                    // TODO : Multi-way conflicts should really be handled in a better way to
                    // resolve the conflict as accurately as possible.
                    let reduceRuleId = TagSet.minElement conflict.Reductions

                    match Map.tryFind terminal settings.TerminalPrecedence,
                          Map.tryFind reduceRuleId settings.RulePrecedence with
                    | None, _
                    | _, None ->
                        // If the precedence/associativity isn't defined for either the terminal
                        // or the production rule, we'll have to handle the conflict using the
                        // default conflict-resolving rules.
                        lr0ParserTable
                    | Some (terminalAssociativity, terminalPrecedence), Some (_, rulePrecedence) ->
                        // The conflict can be resolved if the precedences are different --
                        // we remove the action with lower precedence from this action set. 
                        if terminalPrecedence < rulePrecedence then
                            LrParserTable.RemoveAction (lr0ParserTable, key, Shift targetStateId)
                        elif terminalPrecedence > rulePrecedence then
                            LrParserTable.RemoveAction (lr0ParserTable, key, Reduce reduceRuleId)
                        else
                            // The precedences are the same, so we use the terminal's
                            // associativity to resolve the conflict.
                            match terminalAssociativity with
                            | Left ->
                                // For left-associative tokens, reduce (remove the Shift action).
                                LrParserTable.RemoveAction (lr0ParserTable, key, Shift targetStateId)
                            | Right ->
                                // For right-associative tokens, shift (remove the Reduce action).
                                LrParserTable.RemoveAction (lr0ParserTable, key, Reduce reduceRuleId)
                            | NonAssociative ->
                                // For non-associative tokens, remove *both* actions.
                                { lr0ParserTable with
                                    ActionTable = Map.remove key lr0ParserTable.ActionTable; })

    //
    let resolveConflicts (lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>) =
        //
        (lr0ParserTable, lr0ParserTable.ActionTable)
        ||> Map.fold (fun lr0ParserTable key actionSet ->
            // Does this state contain a conflict?
            match actionSet with
            | Action _ ->
                lr0ParserTable
            | Conflict conflict ->
                // Use the precedence and associativity tables to resolve this conflict (if possible).
                // If the conflict can be resolved, use the LrParserTable.RemoveAction method
                // to remove the action we're not using.
                match conflict.Shift with
                | Some _ ->
                    // Resolve in favor of shifting; this is similar to the
                    // "longest match rule" used in lexical analyzers.
                    // Remove all of the reduce actions from the table.
                    (lr0ParserTable, conflict.Reductions)
                    ||> TagSet.fold (fun lr0ParserTable productionRuleId ->
                        LrParserTable.RemoveAction (lr0ParserTable, key, Reduce productionRuleId))

                | None ->
                    // Resolve in favor of the lowest-numbered rule (i.e., the rule declared first in the grammar).
                    // OPTIMIZE : Use TagSet.extractMin from ExtCore once it's implemented.
                    let resolvedRule = TagSet.minElement conflict.Reductions
                    let reductions = TagSet.remove resolvedRule conflict.Reductions
                    (lr0ParserTable, reductions)
                    ||> TagSet.fold (fun lr0ParserTable productionRuleId ->
                        LrParserTable.RemoveAction (lr0ParserTable, key, Reduce productionRuleId)))

