(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.Tables

open Ast
open Predictive


/// Represents nonterminals augmented with an additional nonterminal
/// representing the start production of an augmented grammar.
type AugmentedNonterminal<'NonterminalId when 'NonterminalId : comparison> =
    /// A nonterminal specified in the original grammar.
    | Nonterminal of 'NonterminalId
    /// Represents the start production of the grammar.
    | Start

    override this.ToString () =
        match this with
        | Nonterminal nonterm ->
            nonterm.ToString ()
        | Start ->
            "\u0002"

//
type AugmentedTerminal<'Token when 'Token : comparison> =
    //
    | Terminal of 'Token
    //
    | EndOfFile

    override this.ToString () =
        match this with
        | Terminal token ->
            token.ToString ()
        | EndOfFile ->
            "\u0003"

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
[<Measure>] type LrParserState
//
type LrParserStateId = int<LrParserState>

//
[<Measure>] type LrReductionRule
//
type LrReductionRuleId = int<LrReductionRule>

//
type LrParserTableAction =
    /// Shift into a state.
    | Shift of LrParserStateId
    /// Goto a state.
    | Goto of LrParserStateId
    /// Reduce by a rule.
    | Reduce of LrReductionRuleId
    /// Accept.
    | Accept

    override this.ToString () =
        match this with
        | Shift stateId ->
            "s" + stateId.ToString ()
        | Goto stateId ->
            "g" + stateId.ToString ()
        | Reduce ruleId ->
            "r" + ruleId.ToString ()
        | Accept ->
            "a"

//
type LrParsingTable<'NonterminalId, 'Token
        when 'NonterminalId : comparison
        and 'Token : comparison> = {
    //
    Table : Map<LrParserStateId * Symbol<'NonterminalId, 'Token>, Set<LrParserTableAction>>;
    //
    ParserStateCount : uint32;
    //
    ReductionRulesById : Map<LrReductionRuleId, 'NonterminalId * Symbol<'NonterminalId, 'Token>[]>;
}

//
type internal Lr0Item<'NonterminalId, 'Token
        when 'NonterminalId : comparison
        and 'Token : comparison> = {
    //
    Nonterminal : 'NonterminalId;
    //
    Production : Symbol<'NonterminalId, 'Token>[];
    //
    Position : int<ParserPosition>;
} with
    override this.ToString () =
        let productionString =
            let sb = System.Text.StringBuilder ()
            for i = 0 to Array.length this.Production do
                if i < int this.Position then
                    this.Production.[i].ToString ()
                    |> sb.Append |> ignore
                elif i = int this.Position then
                    // Append the dot character representing the parser position.
                    sb.Append "\u2022" |> ignore
                else
                    this.Production.[i - 1].ToString ()
                    |> sb.Append |> ignore

            sb.ToString ()

        sprintf "%O \u2192 %s" this.Nonterminal productionString

//
type internal Lr0ParserState<'NonterminalId, 'Token
        when 'NonterminalId : comparison
        and 'Token : comparison> = Set<Lr0Item<'NonterminalId, 'Token>>

/// LR(0) parser table generation state.
type internal Lr0TableGenState<'NonterminalId, 'Token
        when 'NonterminalId : comparison
        and 'Token : comparison> = {
    //
    Table : Map<LrParserStateId * Symbol<'NonterminalId, 'Token>, Set<LrParserTableAction>>;
    //
    ParserStates : Map<Lr0ParserState<'NonterminalId, 'Token>, LrParserStateId>;
    //
    ReductionRules : Map<'NonterminalId * Symbol<'NonterminalId, 'Token>[], LrReductionRuleId>;
    //
    ReductionRulesById : Map<LrReductionRuleId, 'NonterminalId * Symbol<'NonterminalId, 'Token>[]>;
}

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal Lr0TableGenState =
    /// Returns an empty Lr0TableGenState with the given
    /// nonterminal and terminal types.
    let empty : Lr0TableGenState<'NonterminalId, 'Token> = {
        Table = Map.empty;
        ParserStates = Map.empty;
        ReductionRules = Map.empty;
        ReductionRulesById = Map.empty; }

    /// Retrives the identifier for a given parser state (set of items).
    /// If the state has not been assigned an identifier, one is created
    /// and added to the table-generation state before returning.
    let stateId (parserState : Lr0ParserState<'NonterminalId, 'Token>) (tableGenState : Lr0TableGenState<'NonterminalId, 'Token>) =
        // Try to retrieve an existing id for this state.
        match Map.tryFind parserState tableGenState.ParserStates with
        | Some parserStateId ->
            parserStateId, tableGenState

        | None ->
            // Create a new ID for this state.
            let parserStateId = LanguagePrimitives.Int32WithMeasure <| tableGenState.ParserStates.Count + 1

            // Return the id, along with the updated table-gen state.
            parserStateId,
            { tableGenState with
                ParserStates = Map.add parserState parserStateId tableGenState.ParserStates; }

    //
    let reductionRuleId (reductionRule : 'NonterminalId * Symbol<'NonterminalId, 'Token>[]) (tableGenState : Lr0TableGenState<'NonterminalId, 'Token>) =
        // Reduction rules should only be added, but for safety we'll check to
        // see if the rule has already been assigned an identifier.
        match Map.tryFind reductionRule tableGenState.ReductionRules with
        | Some reductionRuleId ->
            reductionRuleId, tableGenState

        | None ->
            // Create a new ID for this reduction rule.
            let reductionRuleId = LanguagePrimitives.Int32WithMeasure <| tableGenState.ReductionRules.Count + 1

            // Return the id, along with the updated table-gen state.
            reductionRuleId,
            { tableGenState with
                ReductionRules = Map.add reductionRule reductionRuleId tableGenState.ReductionRules;
                ReductionRulesById = Map.add reductionRuleId reductionRule tableGenState.ReductionRulesById; }

    /// Add a 'shift' action to the parser table.
    let shift (sourceState : LrParserStateId)
                (transitionSymbol : 'Token)
                (targetState : LrParserStateId)
                (tableGenState : Lr0TableGenState<'NonterminalId, 'Token>) =
        //
        let tableKey = sourceState, Symbol.Terminal transitionSymbol

        //
        let entry =
            let action = Shift targetState
            match Map.tryFind tableKey tableGenState.Table with
            | None ->
                Set.singleton action
            | Some entry ->
                Set.add action entry

        // Update the table with the new entry.
        (),
        { tableGenState with
            Table = Map.add tableKey entry tableGenState.Table; }

    /// Add a 'goto' action to the parser table.
    let goto (sourceState : LrParserStateId)
                (transitionSymbol : 'NonterminalId)
                (targetState : LrParserStateId)
                (tableGenState : Lr0TableGenState<'NonterminalId, 'Token>) =
        //
        let tableKey = sourceState, Symbol.Nonterminal transitionSymbol

        //
        let entry =
            let action = Goto targetState
            match Map.tryFind tableKey tableGenState.Table with
            | None ->
                Set.singleton action
            | Some entry ->
                Set.add action entry

        // Update the table with the new entry.
        (),
        { tableGenState with
            Table = Map.add tableKey entry tableGenState.Table; }

    /// Add an 'accept' action to the parser table.
    let accept (sourceState : LrParserStateId) (tableGenState : Lr0TableGenState<'NonterminalId, AugmentedTerminal<'Token>>) =
        //
        let tableKey = sourceState, Symbol.Terminal EndOfFile

        //
        let entry =
            match Map.tryFind tableKey tableGenState.Table with
            | None ->
                // Create a new 'accept' action for this table entry.
                Set.singleton Accept
            | Some entry ->
                // Create a new 'accept' action and add it to the existing table entry.
                Set.add Accept entry

        // Update the table with the new entry.
        (),
        { tableGenState with
            Table = Map.add tableKey entry tableGenState.Table; }

    /// Add 'reduce' actions to the parser table for each terminal (token) in the grammar.
    let reduce (sourceState : LrParserStateId) (reductionRuleId : LrReductionRuleId) (terminals : Set<_>) (tableGenState : Lr0TableGenState<'NonterminalId, AugmentedTerminal<'Token>>) =
        // Fold over the set of terminals (tokens) in the grammar.
        let table =
            (tableGenState.Table, terminals)
            ||> Set.fold (fun table token ->
                //
                let tableKey = sourceState, Symbol.Terminal token

                //
                let entry =
                    let action = Reduce reductionRuleId
                    match Map.tryFind tableKey table with
                    | None ->
                        Set.singleton action
                    | Some entry ->
                        Set.add action entry

                // Update the table with the entry.
                Map.add tableKey entry table)

        // Return the updated table-gen state.
        (),
        { tableGenState with
            Table = table; }

//
[<RequireQualifiedAccess>]
module Lr0 =
    /// Computes the LR(0) closure of a set of items.
    let internal closure (productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>) items =
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
    let internal goto symbol items (productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>) =
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
    let rec private createTableImpl grammar (tableGenState : Lr0TableGenState<'NonterminalId, AugmentedTerminal<'Token>>) =
        // Preconditions
        assert (not <| Map.isEmpty tableGenState.ParserStates)

        let tableGenState' =
            (tableGenState, tableGenState.ParserStates)
            ||> Map.fold (fun tableGenState stateItems stateId ->
                (tableGenState, stateItems)
                ||> Set.fold (fun tableGenState item ->
                    // If the parser position is at the end of the production,
                    // add a 'reduce' action for every terminal (token) in the grammar.
                    if int item.Position = Array.length item.Production then
                        // First, add this reduction rule to the table-gen state,
                        // which gives us an identifier for the rule.
                        let reductionRuleId, tableGenState =
                            Lr0TableGenState.reductionRuleId (item.Nonterminal, item.Production) tableGenState

                        // Add 'reduce' actions to the parser table.
                        Lr0TableGenState.reduce stateId reductionRuleId grammar.Terminals tableGenState
                        // TEMP : Discard the unit return value until we can use a monadic fold.
                        |> snd
                    else
                        // Add actions to the table based on the next symbol to be parsed.
                        match item.Production.[int item.Position] with
                        | Symbol.Terminal EndOfFile ->
                            // When the end-of-file symbol is the next to be parsed,
                            // add an 'accept' action to the table to indicate the
                            // input has been parsed successfully.
                            Lr0TableGenState.accept stateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Terminal (Terminal _ as token) as symbol ->                            
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                Lr0TableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a terminal (token),
                            // so add a 'shift' action to this entry of the table.
                            Lr0TableGenState.shift stateId token targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Nonterminal nonterm as symbol ->
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                Lr0TableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a nonterminal,
                            // so add a 'goto' action to this entry of the table.
                            Lr0TableGenState.goto stateId nonterm targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd
                        ))
            
        // If any states or transition-edges have been added, we need to recurse
        // and continue until we reach a fixpoint; otherwise, return the completed table.
        if tableGenState.ParserStates <> tableGenState'.ParserStates ||
            tableGenState.Table <> tableGenState'.Table then
            createTableImpl grammar tableGenState'
        else
            // Create the parser table from the table-gen state.
            { Table = tableGenState.Table;
                ParserStateCount = uint32 tableGenState.ParserStates.Count;
                ReductionRulesById = tableGenState.ReductionRulesById; }

    /// Creates an LR(0) parser table from the specified grammar.
    let createTable (grammar : Grammar<'NonterminalId, 'Token>) =
        // Augment the grammar with the start production and end-of-file token.
        let grammar = AugmentedGrammar.ofGrammar grammar

        /// The initial state (set of items) passed to 'createTable'.
        let initialParserState =
            grammar.Productions
            |> Map.find Start
            |> Set.map (fun production ->
                // Create an 'item', with the parser position at
                // the beginning of the production.
                { Nonterminal = Start;
                    Production = production;
                    Position = 0<_>; })
            |> closure grammar.Productions

        // The initial table-gen state.
        let initialParserStateId, initialTableGenState =
            Lr0TableGenState.stateId initialParserState Lr0TableGenState.empty

        // Create the parser table.
        createTableImpl grammar initialTableGenState


// Simple LR (SLR) parser tables.
[<RequireQualifiedAccess>]
module Slr =
    //
    let rec private createTableImpl grammar analysis (tableGenState : Lr0TableGenState<'NonterminalId, AugmentedTerminal<'Token>>) =
        // Preconditions
        assert (not <| Map.isEmpty tableGenState.ParserStates)

        let tableGenState' =
            (tableGenState, tableGenState.ParserStates)
            ||> Map.fold (fun tableGenState stateItems stateId ->
                (tableGenState, stateItems)
                ||> Set.fold (fun tableGenState item ->
                    // If the parser position is at the end of the production,
                    // add a 'reduce' action for every terminal (token) in the grammar.
                    if int item.Position = Array.length item.Production then
                        // First, add this reduction rule to the table-gen state,
                        // which gives us an identifier for the rule.
                        let reductionRuleId, tableGenState =
                            Lr0TableGenState.reductionRuleId (item.Nonterminal, item.Production) tableGenState

                        (*  Simple LR (SLR) parsers only differ from LR(0) parsers in one way:
                            instead of creating 'reduce' actions for all terminals (tokens)
                            in the grammar, we only create them for the tokens in the FOLLOW set
                            of this item's nonterminal. *)

                        let tokens = Map.find item.Nonterminal analysis.Follow                            

                        // Add 'reduce' actions to the parser table.
                        Lr0TableGenState.reduce stateId reductionRuleId tokens tableGenState
                        // TEMP : Discard the unit return value until we can use a monadic fold.
                        |> snd
                    else
                        // Add actions to the table based on the next symbol to be parsed.
                        match item.Production.[int item.Position] with
                        | Symbol.Terminal EndOfFile ->
                            // When the end-of-file symbol is the next to be parsed,
                            // add an 'accept' action to the table to indicate the
                            // input has been parsed successfully.
                            Lr0TableGenState.accept stateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Terminal (Terminal _ as token) as symbol ->                            
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Lr0.goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                Lr0TableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a terminal (token),
                            // so add a 'shift' action to this entry of the table.
                            Lr0TableGenState.shift stateId token targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Nonterminal nonterm as symbol ->
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Lr0.goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                Lr0TableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a nonterminal,
                            // so add a 'goto' action to this entry of the table.
                            Lr0TableGenState.goto stateId nonterm targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd
                        ))
            
        // If any states or transition-edges have been added, we need to recurse
        // and continue until we reach a fixpoint; otherwise, return the completed table.
        if tableGenState.ParserStates <> tableGenState'.ParserStates ||
            tableGenState.Table <> tableGenState'.Table then
            createTableImpl grammar analysis tableGenState'
        else
            // Create the parser table from the table-gen state.
            { Table = tableGenState.Table;
                ParserStateCount = uint32 tableGenState.ParserStates.Count;
                ReductionRulesById = tableGenState.ReductionRulesById; }

    /// Creates a Simple LR (SLR) parser table from the specified grammar.
    let createTable (grammar : Grammar<'NonterminalId, 'Token>) =
        // Augment the grammar with the start production and end-of-file token.
        let grammar = AugmentedGrammar.ofGrammar grammar

        /// Analysis of the augmented grammar.
        let analysis = GrammarAnalysis.ofGrammar grammar

        /// The initial state (set of items) passed to 'createTable'.
        let initialParserState =
            grammar.Productions
            |> Map.find Start
            |> Set.map (fun production ->
                // Create an 'item', with the parser position at
                // the beginning of the production.
                { Nonterminal = Start;
                    Production = production;
                    Position = 0<_>; })
            |> Lr0.closure grammar.Productions

        // The initial table-gen state.
        let initialParserStateId, initialTableGenState =
            Lr0TableGenState.stateId initialParserState Lr0TableGenState.empty

        // Create the parser table.
        createTableImpl grammar analysis initialTableGenState


//
type internal Lr1Item<'NonterminalId, 'Token
        when 'NonterminalId : comparison
        and 'Token : comparison> = {
    //
    Nonterminal : 'NonterminalId;
    //
    Production : Symbol<'NonterminalId, 'Token>[];
    //
    Position : int<ParserPosition>;
    //
    LookaheadSymbol : 'Token;
} with
    override this.ToString () =
        let productionString =
            let sb = System.Text.StringBuilder ()
            for i = 0 to Array.length this.Production do
                if i < int this.Position then
                    this.Production.[i].ToString ()
                    |> sb.Append |> ignore
                elif i = int this.Position then
                    // Append the dot character representing the parser position.
                    sb.Append "\u2022" |> ignore
                else
                    this.Production.[i - 1].ToString ()
                    |> sb.Append |> ignore

            sb.ToString ()

        sprintf "%O \u2192 %s, %O" this.Nonterminal productionString this.LookaheadSymbol

