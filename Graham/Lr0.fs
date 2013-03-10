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

//
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

        /// Computes the LR(0) closure of a set of items.
        // OPTIMIZE : Modify this to use a worklist-style algorithm to avoid
        // reprocessing items which already exist in the set (i.e., when iterating,
        // we only process items added to the set in the previous iteration).
        let closure (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) items =
            /// Implementation of the LR(0) closure algorithm.
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
                                let nontermProductions = Map.find nontermId productions

                                // For all productions of this nonterminal, create a new item
                                // with the parser position at the beginning of the production.
                                // Add these new items into the set of items.
                                (items, nontermProductions)
                                ||> Array.fold (fun items production ->
                                    let newItem = {
                                        Nonterminal = nontermId;
                                        Production = production;
                                        Position = GenericZero;
                                        Lookahead = (); }

                                    Set.add newItem items))

                // If the items set has changed, recurse for another iteration.
                // If not, we're done processing and the set is returned.
                if items' = items then
                    items
                else
                    closure items'

            // Compute the closure, starting with the specified initial items.
            closure items

        /// Moves the 'dot' (the current parser position) past the
        /// specified symbol for each item in a set of items.
        let goto symbol items (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) =
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
            |> closure productions


    //
    let rec private createTableImpl (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) workSet (tableGenState : Lr0TableGenState<_,_>) =
        // If the work-set is empty, we're done creating the table.
        if Set.isEmpty workSet then
            tableGenState
        else
            ((Set.empty, tableGenState), workSet)
            ||> Set.fold (fun workSet_tableGenState stateId ->
                /// The set of parser items for this state.
                let stateItems = Map.find stateId (snd tableGenState).ParserStates

                (workSet_tableGenState, stateItems)
                ||> Set.fold (fun (workSet, ((_, env) as tableGenState)) item ->
                    // If the parser position is at the end of the production,
                    // add a 'reduce' action for every terminal (token) in the grammar.
                    if int item.Position = Array.length item.Production then
                        /// The production rule identifier for this production.
                        let productionRuleId =
                            // Get the production-rule-id from the 'environment' component of the table-generation state.
                            let productionKey = (item.Nonterminal, item.Production)
                            Map.find productionKey (fst tableGenState).ProductionRuleIds

                        // Add a 'reduce' action to the ACTION table for each terminal (token) in the grammar.
                        workSet,
                        (tableGenState, grammar.Terminals)
                        ||> Set.fold (fun tableGenState terminal ->
                            let key = stateId, terminal
                            LrTableGenState.reduce key productionRuleId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd)
                    else
                        // Add actions to the table based on the next symbol to be parsed.
                        match item.Production.[int item.Position] with
                        | Symbol.Terminal EndOfFile ->
                            // When the end-of-file symbol is the next to be parsed,
                            // add an 'accept' action to the table to indicate the
                            // input has been parsed successfully.
                            workSet,
                            LrTableGenState.accept stateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Terminal (Terminal _ as token) as symbol ->
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Item.goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let (isNewState, targetStateId), tableGenState =
                                LrTableGenState.stateId targetState tableGenState

                            // If this is a new state, add it to the list of states which need to be visited.
                            let workSet =
                                if isNewState then
                                    Set.add targetStateId workSet
                                else workSet

                            // The next symbol to be parsed is a terminal (token),
                            // so add a 'shift' action to this entry of the table.
                            workSet,
                            LrTableGenState.shift (stateId, token) targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Nonterminal nonterm as symbol ->
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Item.goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let (isNewState, targetStateId), tableGenState =
                                LrTableGenState.stateId targetState tableGenState

                            // If this is a new state, add it to the list of states which need to be visited.
                            let workSet =
                                if isNewState then
                                    Set.add targetStateId workSet
                                else workSet

                            // The next symbol to be parsed is a nonterminal,
                            // so add a 'goto' action to this entry of the table.
                            workSet,
                            LrTableGenState.goto (stateId, nonterm) targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd
                        ))
            // Recurse with the updated table-generation state and work-set.
            ||> createTableImpl grammar

    /// Creates an LR(0) parser table from the specified grammar.
    let createTable (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) : Lr0ParserTable<'Nonterminal, 'Terminal> =
        // Preconditions
        // TODO

        // The initial table-generation state.
        let (_, initialParserStateId), tableGenState =
            //
            let tableGenState =
                LrTableGenState.empty
                // Add the production rules to the environment.
                |> LrTableGenState.setProductionRules grammar.Productions
                // TEMP : Discard the unit return value until we rewrite this with the State workflow.
                |> snd

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
                |> Item.closure grammar.Productions

            LrTableGenState.stateId initialParserState tableGenState
            
        // Create the parser table.
        createTableImpl grammar (Set.singleton initialParserStateId) tableGenState
        // Get the table from the table-generation state.
        |> snd

    //
    let applyPrecedence (lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>,
                         settings : PrecedenceSettings<'Terminal>) : Lr0ParserTable<'Nonterminal, 'Terminal> =
        // Fold over the provided table, using the supplied precedence and
        // associativity tables to resolve conflicts wherever possible.
        (lr0ParserTable, lr0ParserTable.ActionTable)
        ||> Map.fold (fun lr0ParserTable ((stateId, terminal) as key) actionSet ->
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
                        raise <| exn "Found a conflict involving the end-of-file marker."
                    | Terminal terminal ->
                        terminal

                // Use the precedence and associativity tables to resolve this conflict (if possible).
                // If the conflict can be resolved, use the LrParserTable.RemoveAction method
                // to remove the action we're not using.
                match conflict with
                | ReduceReduce (_,_) ->
                    (*  Reduce-reduce conflicts aren't solved with precedence/associativity --
                        instead, they must be resolved by the 'resolveConflicts' function. *)
                    lr0ParserTable

                | ShiftReduce (targetStateId, reduceRuleId) ->
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
        ||> Map.fold (fun lr0ParserTable ((stateId, terminal) as key) actionSet ->
            // Does this state contain a conflict?
            match actionSet with
            | Action _ ->
                lr0ParserTable
            | Conflict conflict ->
                // Use the precedence and associativity tables to resolve this conflict (if possible).
                // If the conflict can be resolved, use the LrParserTable.RemoveAction method
                // to remove the action we're not using.
                match conflict with
                | ReduceReduce (reduceRuleId1, reduceRuleId2) ->
                    // Resolve in favor of the lower-numbered rule (i.e., the rule declared first in the grammar).
                    if reduceRuleId1 < reduceRuleId2 then
                        LrParserTable.RemoveAction (lr0ParserTable, key, Reduce reduceRuleId2)
                    elif reduceRuleId1 > reduceRuleId2 then
                        LrParserTable.RemoveAction (lr0ParserTable, key, Reduce reduceRuleId1)
                    else
                        // This shouldn't ever happen, unless someone goes
                        // out of their way to create such an entry.
                        lr0ParserTable

                | ShiftReduce (targetStateId, reduceRuleId) ->
                    // Resolve in favor of shifting; this is similar to the
                    // "longest match rule" used in lexical analyzers.
                    LrParserTable.RemoveAction (lr0ParserTable, key, Reduce reduceRuleId))

