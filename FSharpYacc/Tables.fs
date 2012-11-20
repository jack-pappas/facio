(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.Tables

open Ast
open Derivation


//
[<Measure>] type LrParsingState
//
type LrParsingStateId = int<LrParsingState>

//
[<Measure>] type LrParsingRule
//
type LrParsingRuleId = int<LrParsingRule>

//
type LrParsingTableEntry =
    /// Shift into a state.
    | Shift of LrParsingStateId
    /// Goto a state.
    | Goto of LrParsingStateId
    /// Reduce by a rule.
    | Reduce of LrParsingRuleId
    /// Accept.
    | Accept

//
type LrParsingTable<'NonterminalId, 'Token
        when 'NonterminalId : comparison
        and 'Token : comparison> = {
    //
    Table : Map<LrParsingStateId * Symbol<'NonterminalId, 'Token>, LrParsingTableEntry>;
//    //
//    ReductionRules : Map<LrParsingRuleId, 'NonterminalId * Symbol<'NonterminalId, 'Token>>;
}

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LrParsingTable =
    //
    let empty : LrParsingTable<'NonterminalId, 'Token> = {
        Table = Map.empty;
        //ReductionRules = Map.empty;
        }

    //
    let inline tryFind state symbol (table : LrParsingTable<'NonterminalId, 'Token>) =
        Map.tryFind (state, symbol) table.Table

    //
    let inline add state symbol entry (table : LrParsingTable<'NonterminalId, 'Token>) =
        { table with
            Table = Map.add (state, symbol) entry table.Table; }


/// Represents nonterminals augmented with an additional nonterminal
/// representing the start production of an augmented grammar.
type AugmentedNonterminal<'NonterminalId when 'NonterminalId : comparison> =
    /// A nonterminal specified in the original grammar.
    | Nonterminal of 'NonterminalId
    /// Represents the start production of the grammar.
    | Start

//
type AugmentedTerminal<'Token when 'Token : comparison> =
    //
    | Terminal of 'Token
    //
    | EndOfFile

//
[<RequireQualifiedAccess>]
module AugmentedGrammar =
    //
    let ofGrammar (grammar : Grammar<'NonterminalId, 'Token>)
        : Grammar<AugmentedNonterminal<'NonterminalId>, AugmentedTerminal<'Token>> =
        // Based on the input grammar, create a new grammar with an additional
        // nonterminal and production for the start symbol and an additional token
        // representing the end-of-file marker.
        let startProduction = [|
            Symbol.Nonterminal <| Nonterminal grammar.StartSymbol;
            Symbol.Terminal EndOfFile; |]

        {   StartSymbol = Start;
            Terminals =
                grammar.Terminals
                |> Set.map Terminal
                |> Set.add EndOfFile;
            Nonterminals =
                grammar.Nonterminals
                |> Set.map Nonterminal
                |> Set.add Start;
            Productions =
                (Map.empty, grammar.Productions)
                ||> Map.fold (fun productionMap nontermId nontermProductions ->
                    let nontermProductions =
                        nontermProductions
                        |> Set.map (Array.map (function
                            | Symbol.Nonterminal nontermId ->
                                Symbol.Nonterminal <| Nonterminal nontermId
                            | Symbol.Terminal token ->
                                Symbol.Terminal <| Terminal token))
                    Map.add (Nonterminal nontermId) nontermProductions productionMap)
                // Add the (only) production of the new start symbol.
                |> Map.add Start (Set.singleton startProduction); }

/// Represents the position of a parser in a production.
/// The position corresponds to the 0-based index of the next symbol
/// to be parsed, so position values must always be within the range
/// [0, production.Length].
[<Measure>] type ParserPosition

//
[<RequireQualifiedAccess>]
module Lr0 =
    //
    type private Lr0Item<'NonterminalId, 'Token
            when 'NonterminalId : comparison
            and 'Token : comparison> = {
        //
        Nonterminal : 'NonterminalId;
        //
        Production : Symbol<'NonterminalId, 'Token>[];
        //
        Position : int<ParserPosition>;
    }
    
    /// Computes the LR(0) closure of a set of items.
    let private closure (productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>) items =
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
                            ||> Set.fold (fun items production ->
                                let newItem = {
                                    Nonterminal = nontermId;
                                    Production = production;
                                    Position = 0<_>; }

                                Set.add newItem items))

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
    let private goto symbol items (productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>) =
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
        closure productions items

    //
    // TODO : Instead of 'states' and 'edges' arguments, modify this to
    // use an immutable graph type -- the states are the vertices of the graph.
    let rec private createParserTransitions (states : Set<Set<Lr0Item<_,_>>>) edges productions =
        let states', edges' =
            ((states, edges), states)
            ||> Set.fold (fun (states, edges) state ->
                ((states, edges), state)
                ||> Set.fold (fun (states, edges) item ->
                    // If the parser position is at the end of the production,
                    // there's nothing we need to do with this item.
                    if int item.Position = Array.length item.Production then
                        states, edges
                    else
                        match item.Production.[int item.Position] with
                        | Symbol.Terminal EndOfFile ->
                            // For the end-of-file symbol, don't do anything now --
                            // we'll add an 'accept' action later when creating the table.
                            states, edges

                        | symbol ->
                            /// The state (set of items) transitioned into via the
                            /// edge labeled with this symbol.
                            let targetState = goto symbol state productions

                            // Add the target state into the set of states.
                            let states = Set.add targetState states

                            // Add an edge, labeled with this symbol, from the current state
                            // to the target state.
                            let edges = Map.add (state, targetState) symbol edges
                                
                            // Continue processing.
                            states, edges))
            
        // If either 'states' or 'edges' has been updated, we recurse and process
        // them again; otherwise, return them.
        if states <> states' ||
            edges <> edges' then
            createParserTransitions states' edges' productions
        else
            states, edges

    //
    let createTable (grammar : Grammar<'NonterminalId, 'Token>) =
        // Augment the grammar with the start production and end-of-file token.
        let grammar = AugmentedGrammar.ofGrammar grammar

        /// The initial state (set of items) passed to 'createTable'.
        let initialState =
            grammar.Productions
            |> Map.find Start
            |> Set.map (fun production ->
                // Create an 'item', with the parser position at
                // the beginning of the production.
                { Nonterminal = Start;
                    Production = production;
                    Position = 0<_>; })
            |> closure grammar.Productions

        // Create the transition graph for the parser automaton.
        // The labels on the transition edges determine whether the transition
        // represents a 'shift' or 'goto' action.
        let parserStates, transitionEdges =
            createParserTransitions (Set.singleton initialState) Map.empty grammar.Productions

        /// Id numbers for the parser states.
        let parserStateIdentifiers =
            (Map.empty, parserStates)
            ||> Set.fold (fun parserStateIdentifiers parserState ->
                /// The identifier for this parser state.
                let parserStateId : LrParsingStateId =
                    LanguagePrimitives.Int32WithMeasure parserStateIdentifiers.Count

                // Add this state and it's identifier to the map.
                Map.add parserState parserStateId parserStateIdentifiers)

        // Compute the set of LR(0) 'reduce' actions.
        let reduceActions, reductionRules =
            /// Maps states to the production reduced by that state.
            let reduceActions =
                (Map.empty, parserStates)
                ||> Set.fold (fun reduceActions parserState ->
                    (reduceActions, parserState)
                    ||> Set.fold (fun reduceActions item ->
                        // If the parser position is at the end of the production,
                        // then this state will perform a 'reduce' action.
                        if int item.Position = Array.length item.Production then
                            Map.add parserState (item.Nonterminal, item.Production) reduceActions
                        else
                            reduceActions))

            // Assign a unique rule ID to each reduction rule to make
            // it easier to work with in the parsing table.
            ((Map.empty, Map.empty), reduceActions)
            ||> Map.fold (fun (reduceActions, reductionRules) parserState rule ->
                /// The identifier for this rule.
                let ruleId : LrParsingRuleId = LanguagePrimitives.Int32WithMeasure reductionRules.Count

                // Add entries to the maps.
                Map.add parserState ruleId reduceActions,
                Map.add ruleId rule reductionRules)

        // Determine where to put the 'accept' action.
        // For simplicity, we compute this as if there could be multiple
        // accept states; however, unless something goes wrong, we'll only
        // ever have a single 'accept' action in the parser table.
        let acceptingStates =
            (Set.empty, parserStates)
            ||> Set.fold (fun acceptingStates parserState ->
                (acceptingStates, parserState)
                ||> Set.fold (fun acceptingStates item ->
                    // If the parser position is at the end of the production,
                    // there's nothing to do.
                    if int item.Position = Array.length item.Production then
                        acceptingStates
                    else
                        // If the next symbol to be parsed is the end-of-file marker,
                        // then this is the 'accept' state.
                        match item.Production.[int item.Position] with
                        | Symbol.Terminal EndOfFile ->
                            // Add this state to the set of accepting states.
                            Set.add parserState acceptingStates
                        | _ ->
                            // This state is not an accepting state.
                            acceptingStates))

        (* Use the computed data to construct the parser table. *)
        let parserTable = ()
            
        



        raise <| System.NotImplementedException "Lr0.createTable"
        ()



 

//    let test (grammar : Grammar<_,_>) =
//        let state3StartItem = {
//            Nonterminal = 'S';
//            Production =
//                [|
//                Ast.Terminal "(";
//                Ast.Nonterminal 'L';
//                Ast.Terminal ")"; |]
//            Position = 1<_>; }
//
//        let state3Closure =
//            closure (Set.singleton state3StartItem) grammar.Productions
//
//        ()


