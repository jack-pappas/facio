(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.LR

open Grammar
open Analysis


/// An action which manipulates the state of the
/// parser automaton for an LR(k) parser.
type LrParserAction =
    /// Shift into a state.
    | Shift of ParserStateId
    /// Goto a state.
    | Goto of ParserStateId
    /// Reduce by a production rule.
    | Reduce of ReductionRuleId
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
type LrParsingTable<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    //
    Table : Map<ParserStateId * Symbol<'Nonterminal, 'Terminal>, Set<LrParserAction>>;
    //
    ParserStateCount : uint32;
    //
    ReductionRulesById : Map<ReductionRuleId, 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]>;
}

/// An LR(k) item.
type internal LrItem<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    //
    Nonterminal : 'Nonterminal;
    //
    Production : Symbol<'Nonterminal, 'Terminal>[];
    //
    Position : int<ParserPosition>;
    //
    Lookahead : 'Lookahead;
} with
    override this.ToString () =
        let sb = System.Text.StringBuilder ()

        // Add the nonterminal text and arrow to the StringBuilder.
        sprintf "%O \u2192 " this.Nonterminal
        |> sb.Append |> ignore

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

        // Append the lookahead symbol, if applicable.
        if typeof<'Lookahead> <> typeof<unit> then
            sb.Append ", " |> ignore
            this.Lookahead.ToString () |> sb.Append |> ignore

        sb.ToString ()


/// An LR(0) item.
type internal Lr0Item<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrItem<'Nonterminal, 'Terminal, unit>

/// Functions for manipulating LR(0) parser items.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal Lr0Item =
    /// Computes the LR(0) closure of a set of items.
    // TODO : Modify this to use a worklist-style algorithm to avoid
    // reprocessing items which already exist in the set (i.e., when iterating,
    // we only process items added to the set in the previous iteration).
    let closure (productions : Map<'Nonterminal, Set<Symbol<'Nonterminal, 'Terminal>[]>>) items =
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
                                    Position = 0<_>;
                                    Lookahead = (); }

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
    let goto symbol items (productions : Map<'Nonterminal, Set<Symbol<'Nonterminal, 'Terminal>[]>>) =
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


/// An LR(0) parser state -- i.e., a set of LR(0) items.
type internal Lr0ParserState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = Set<Lr0Item<'Nonterminal, 'Terminal>>

/// LR(0) parser table generation state.
type internal Lr0TableGenState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    //
    Table : Map<ParserStateId * Symbol<'Nonterminal, 'Terminal>, Set<LrParserAction>>;
    //
    ParserStates : Map<Lr0ParserState<'Nonterminal, 'Terminal>, ParserStateId>;
    //
    ReductionRules : Map<'Nonterminal * Symbol<'Nonterminal, 'Terminal>[], ReductionRuleId>;
    //
    ReductionRulesById : Map<ReductionRuleId, 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]>;
}

/// Functions which use the State monad to manipulate an LR(0) table-generation state.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal Lr0TableGenState =
    /// Returns an empty Lr0TableGenState with the given
    /// nonterminal and terminal types.
    let empty : Lr0TableGenState<'Nonterminal, 'Terminal> = {
        Table = Map.empty;
        ParserStates = Map.empty;
        ReductionRules = Map.empty;
        ReductionRulesById = Map.empty; }

    /// Retrives the identifier for a given parser state (set of items).
    /// If the state has not been assigned an identifier, one is created
    /// and added to the table-generation state before returning.
    let stateId (parserState : Lr0ParserState<'Nonterminal, 'Terminal>) (tableGenState : Lr0TableGenState<'Nonterminal, 'Terminal>) =
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
    let reductionRuleId (reductionRule : 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]) (tableGenState : Lr0TableGenState<'Nonterminal, 'Terminal>) =
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
    let shift (sourceState : ParserStateId)
                (transitionSymbol : 'Terminal)
                (targetState : ParserStateId)
                (tableGenState : Lr0TableGenState<'Nonterminal, 'Terminal>) =
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
    let goto (sourceState : ParserStateId)
                (transitionSymbol : 'Nonterminal)
                (targetState : ParserStateId)
                (tableGenState : Lr0TableGenState<'Nonterminal, 'Terminal>) =
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
    let accept (sourceState : ParserStateId) (tableGenState : Lr0TableGenState<'Nonterminal, AugmentedTerminal<'Terminal>>) =
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
    let reduce (sourceState : ParserStateId) (reductionRuleId : ReductionRuleId) (terminals : Set<_>) (tableGenState : Lr0TableGenState<'Nonterminal, AugmentedTerminal<'Terminal>>) =
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

/// LR(0) parser tables.
[<RequireQualifiedAccess>]
module internal Lr0 =
    //
    let rec private createTableImpl grammar (tableGenState : Lr0TableGenState<'Nonterminal, AugmentedTerminal<'Terminal>>) =
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
                            let targetState = Lr0Item.goto symbol stateItems grammar.Productions

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
                            let targetState = Lr0Item.goto symbol stateItems grammar.Productions

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
    let createTable (grammar : Grammar<'Nonterminal, 'Terminal>) =
        // Augment the grammar with the start production and end-of-file token.
        let grammar = Grammar.augment grammar

        /// The initial state (set of items) passed to 'createTable'.
        let initialParserState =
            grammar.Productions
            |> Map.find Start
            |> Set.map (fun production ->
                // Create an 'item', with the parser position at
                // the beginning of the production.
                {   Nonterminal = Start;
                    Production = production;
                    Position = 0<_>;
                    Lookahead = (); })
            |> Lr0Item.closure grammar.Productions

        // The initial table-gen state.
        let initialParserStateId, initialTableGenState =
            Lr0TableGenState.stateId initialParserState Lr0TableGenState.empty

        // Create the parser table.
        createTableImpl grammar initialTableGenState


// Simple LR (SLR) parser tables.
[<RequireQualifiedAccess>]
module Slr =
    //
    let rec private createTableImpl (grammar : Grammar<_,_>) analysis (tableGenState : Lr0TableGenState<'Nonterminal, AugmentedTerminal<'Terminal>>) =
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
                            let targetState = Lr0Item.goto symbol stateItems grammar.Productions

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
                            let targetState = Lr0Item.goto symbol stateItems grammar.Productions

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
    let createTable (grammar : Grammar<'Nonterminal, 'Terminal>) =
        // Augment the grammar with the start production and end-of-file token.
        let grammar = Grammar.augment grammar

        /// Predictive sets of the augmented grammar.
        let analysis = PredictiveSets.ofGrammar grammar

        /// The initial state (set of items) passed to 'createTable'.
        let initialParserState =
            grammar.Productions
            |> Map.find Start
            |> Set.map (fun production ->
                // Create an 'item', with the parser position at
                // the beginning of the production.
                {   Nonterminal = Start;
                    Production = production;
                    Position = 0<_>;
                    Lookahead = (); })
            |> Lr0Item.closure grammar.Productions

        // The initial table-gen state.
        let initialParserStateId, initialTableGenState =
            Lr0TableGenState.stateId initialParserState Lr0TableGenState.empty

        // Create the parser table.
        createTableImpl grammar analysis initialTableGenState


/// An LR(1) item.
type internal Lr1Item<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrItem<'Nonterminal, 'Terminal, 'Terminal>

/// Functions for manipulating LR(1) parser items.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal Lr1Item =
    /// Computes the FIRST set of a string of symbols.
    /// The string is a "substring" of a production, followed by a lookahead token.
    let firstSetOfString (production : Symbol<'Nonterminal, 'Terminal>[]) startIndex (lookahead : 'Terminal) (predictiveSets : PredictiveSets<'Nonterminal, 'Terminal>) : Set<'Terminal> =
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
    let closure (grammar : Grammar<'Nonterminal, 'Terminal>) (predictiveSets : PredictiveSets<'Nonterminal, 'Terminal>) items =
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
                            ||> Set.fold (fun items production ->
                                // Combine the production with each token which could
                                // possibly follow this nonterminal.
                                (items, firstSetOfRemainingSymbols)
                                ||> Set.fold (fun items nontermFollowToken ->
                                    let newItem = {
                                        Nonterminal = nontermId;
                                        Production = production;
                                        Position = 0<_>;
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
    let goto symbol items (grammar : Grammar<'Nonterminal, 'Terminal>) (predictiveSets : PredictiveSets<_,_>) =
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


/// An LR(1) parser state -- i.e., a set of LR(1) items.
type internal Lr1ParserState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    Set<Lr1Item<'Nonterminal, 'Terminal>>

/// LR(1) parser table generation state.
type internal Lr1TableGenState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    //
    Table : Map<ParserStateId * Symbol<'Nonterminal, 'Terminal>, Set<LrParserAction>>;
    //
    ParserStates : Map<Lr1ParserState<'Nonterminal, 'Terminal>, ParserStateId>;
    //
    ReductionRules : Map<'Nonterminal * Symbol<'Nonterminal, 'Terminal>[], ReductionRuleId>;
    //
    ReductionRulesById : Map<ReductionRuleId, 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]>;
}

/// Functions which use the State monad to manipulate an LR(1) table-generation state.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal Lr1TableGenState =
    /// Returns an empty Lr1TableGenState with the given
    /// nonterminal and terminal types.
    let empty : Lr1TableGenState<'Nonterminal, 'Terminal> = {
        Table = Map.empty;
        ParserStates = Map.empty;
        ReductionRules = Map.empty;
        ReductionRulesById = Map.empty; }

    /// Retrives the identifier for a given parser state (set of items).
    /// If the state has not been assigned an identifier, one is created
    /// and added to the table-generation state before returning.
    let stateId (parserState : Lr1ParserState<'Nonterminal, 'Terminal>) (tableGenState : Lr1TableGenState<'Nonterminal, 'Terminal>) =
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
    let reductionRuleId (reductionRule : 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]) (tableGenState : Lr1TableGenState<'Nonterminal, 'Terminal>) =
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
    let shift (sourceState : ParserStateId)
                (transitionSymbol : 'Terminal)
                (targetState : ParserStateId)
                (tableGenState : Lr1TableGenState<'Nonterminal, 'Terminal>) =
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
    let goto (sourceState : ParserStateId)
                (transitionSymbol : 'Nonterminal)
                (targetState : ParserStateId)
                (tableGenState : Lr1TableGenState<'Nonterminal, 'Terminal>) =
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
    let accept (sourceState : ParserStateId) (tableGenState : Lr1TableGenState<'Nonterminal, AugmentedTerminal<'Terminal>>) =
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

    /// Add a 'reduce' action to the parser table for the specified lookahead token.
    let reduce (sourceState : ParserStateId) (reductionRuleId : ReductionRuleId) (lookaheadToken : AugmentedTerminal<'Terminal>) (tableGenState : Lr1TableGenState<'Nonterminal, AugmentedTerminal<'Terminal>>) =
        //
        let tableKey = sourceState, Symbol.Terminal lookaheadToken

        //
        let entry =
            let action = Reduce reductionRuleId
            match Map.tryFind tableKey tableGenState.Table with
            | None ->
                Set.singleton action
            | Some entry ->
                Set.add action entry

        // Update the table with the new entry.
        (),
        { tableGenState with
            Table = Map.add tableKey entry tableGenState.Table; }


/// LR(1) parser tables.
[<RequireQualifiedAccess>]
module Lr1 =
    //
    let rec private createTableImpl grammar predictiveSets (tableGenState : Lr1TableGenState<'Nonterminal, AugmentedTerminal<'Terminal>>) =
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
                            Lr1TableGenState.reductionRuleId (item.Nonterminal, item.Production) tableGenState

                        // Add a 'reduce' action for the entry with this state and lookahead token.
                        Lr1TableGenState.reduce stateId reductionRuleId item.Lookahead tableGenState
                        // TEMP : Discard the unit return value until we can use a monadic fold.
                        |> snd
                    else
                        // Add actions to the table based on the next symbol to be parsed.
                        match item.Production.[int item.Position] with
                        | Symbol.Terminal EndOfFile ->
                            // When the end-of-file symbol is the next to be parsed,
                            // add an 'accept' action to the table to indicate the
                            // input has been parsed successfully.
                            Lr1TableGenState.accept stateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Terminal (Terminal _ as token) as symbol ->                            
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Lr1Item.goto symbol stateItems grammar predictiveSets

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                Lr1TableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a terminal (token),
                            // so add a 'shift' action to this entry of the table.
                            Lr1TableGenState.shift stateId token targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Nonterminal nonterm as symbol ->
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Lr1Item.goto symbol stateItems grammar predictiveSets

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                Lr1TableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a nonterminal,
                            // so add a 'goto' action to this entry of the table.
                            Lr1TableGenState.goto stateId nonterm targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd
                        ))
            
        // If any states or transition-edges have been added, we need to recurse
        // and continue until we reach a fixpoint; otherwise, return the completed table.
        if tableGenState.ParserStates <> tableGenState'.ParserStates ||
            tableGenState.Table <> tableGenState'.Table then
            createTableImpl grammar predictiveSets tableGenState'
        else
            // Return the table-gen state itself -- the consuming method
            // can construct the table from it.
            tableGenState

    //
    let private createTableGenState (grammar : Grammar<'Nonterminal, 'Terminal>) =
        // Augment the grammar with the start production and end-of-file token.
        let grammar = Grammar.augment grammar

        /// Analysis of the augmented grammar.
        let predictiveSets = PredictiveSets.ofGrammar grammar

        /// The initial state (set of items) passed to 'createTable'.
        let initialParserState : Lr1ParserState<_,_> =
            let startProductions = Map.find Start grammar.Productions
            (Set.empty, startProductions)
            ||> Set.fold (fun items production ->
                // Create an 'item', with the parser position at
                // the beginning of the production.
                let item = {
                    Nonterminal = Start;
                    Production = production;
                    Position = 0<_>;
                    // Any token can be used here, because the end-of-file symbol
                    // (in the augmented start production) will never be shifted.
                    // We use the EndOfFile token itself here to keep the code generic.
                    Lookahead = EndOfFile; }
                Set.add item items)
            |> Lr1Item.closure grammar predictiveSets

        // The initial table-gen state.
        let initialParserStateId, initialTableGenState =
            Lr1TableGenState.stateId initialParserState Lr1TableGenState.empty

        // Create the table-gen state.
        createTableImpl grammar predictiveSets initialTableGenState

    /// Create an LR(1) parser table for the specified grammar.
    let createTable (grammar : Grammar<'Nonterminal, 'Terminal>) =
        // Create the table-gen state.
        let tableGenState = createTableGenState grammar

        // Create the LR(1) parser table from the table-gen state.
        {   Table = tableGenState.Table;
            ParserStateCount = uint32 tableGenState.ParserStates.Count;
            ReductionRulesById = tableGenState.ReductionRulesById; }

    /// Create a LALR(1) action from an LR(1) action.
    let private lalrAction lrToLalrIdMap lrAction =
        match lrAction with
        | Shift lrParserStateId ->
            Shift <| Map.find lrParserStateId lrToLalrIdMap
        | Goto lrParserStateId ->
            Goto <| Map.find lrParserStateId lrToLalrIdMap
        // These actions don't change
        | Reduce _
        | Accept as action ->
            action

    /// <summary>An LR(1) parser state (set of LR(1) items) without lookahead tokens.</summary>
    /// <remarks>Uses the Lr0Item type because it has the exact same fields as Lr1Item
    /// when the lookahead token is discarded, and therefore we avoid creating a type
    /// which would be exactly the same except for it's semantics.</remarks>
    type private Lr1ParserStateNoLookahead<'Nonterminal, 'Terminal
        when 'Nonterminal : comparison
        and 'Terminal : comparison> = Set<Lr0Item<'Nonterminal, 'Terminal>>

    /// Discards the lookahead tokens from the items in an LR(1) parser state.
    let private discardLookaheadTokens (lr1ParserState : Lr1ParserState<'Nonterminal, 'Terminal>)
        : Lr1ParserStateNoLookahead<'Nonterminal, 'Terminal> =
        lr1ParserState
        |> Set.map (fun lr1Item ->
            {   Nonterminal = lr1Item.Nonterminal;
                Production = lr1Item.Production;
                Position = lr1Item.Position;
                Lookahead = (); } : Lr0Item<_,_>)

    /// Create a LALR(1) parser table for the specified grammar.
    let createCompressedTable (grammar : Grammar<'Nonterminal, 'Terminal>) =
        // Create the table-gen state.
        let tableGenState = createTableGenState grammar

        // Fold over the LR(1) table-gen state to determine which LR(1) states
        // (sets of LR(1) items) are equivalent except for their lookahead
        // tokens. The resulting merged states are the LALR(1) states.
        /// Maps LR(1) state identifiers to LALR(1) state identifiers.
        let lrToLalrIdMap, lalrParserStateCount =
            let lrToLalrIdMap, noLookaheadStateIdMap =
                ((Map.empty, Map.empty), tableGenState.ParserStates)
                // lrToLalrIdMap -- Maps LR(1) state identifiers to LALR(1) state identifiers.
                // noLookaheadStateIdMap -- Maps LR(1) states whose lookahead tokens have been
                // discarded to the LALR(1) state identifier representing that state and any
                // other equivalent states which have been merged into it.
                ||> Map.fold (fun (lrToLalrIdMap, noLookaheadStateIdMap : Map<Lr1ParserStateNoLookahead<_,_>, ParserStateId>) lrParserState lrParserStateId ->
                    /// The LALR(1) state identifier for this LR(1) state.
                    let lalrParserStateId, noLookaheadStateIdMap =
                        /// The items of this LR(1) state, without their lookahead tokens.
                        let lrParserStateNoLookahead = discardLookaheadTokens lrParserState

                        // Find the LALR(1) state id for this LR(1) state without lookahead tokens.
                        // If no state id has been created for it yet, create one and add it to the map.
                        match Map.tryFind lrParserStateNoLookahead noLookaheadStateIdMap with
                        | Some lalrParserStateId ->
                            lalrParserStateId, noLookaheadStateIdMap
                        | None ->
                            // Create a new LALR(1) state identifier for this state.
                            let lalrParserStateId : ParserStateId =
                                LanguagePrimitives.Int32WithMeasure <| noLookaheadStateIdMap.Count + 1

                            // Add this state and it's identifier to the map.
                            let noLookaheadStateIdMap =
                                Map.add lrParserStateNoLookahead lalrParserStateId noLookaheadStateIdMap

                            // Return the state identifier and the updated map.
                            lalrParserStateId, noLookaheadStateIdMap

                    // Add an entry to the LR(1) -> LALR(1) state id map.
                    let lrToLalrIdMap = Map.add lrParserStateId lalrParserStateId lrToLalrIdMap                     

                    // Pass the maps to the next iteration of the folds.
                    lrToLalrIdMap,
                    noLookaheadStateIdMap)

            // The 'noLookaheadStateIdMap' isn't needed any longer, but we need the
            // number of entries to include in the parser table record.
            lrToLalrIdMap, uint32 noLookaheadStateIdMap.Count

        // Using the LR(1) to LALR(1) state-id map, create a
        // LALR(1) parser table from the LR(1) parser table.
        let lalrTable =
            (Map.empty, tableGenState.Table)
            ||> Map.fold (fun lalrTable (lrParserStateId, lookaheadToken) lrActions ->
                /// The LALR(1) state identifier for this LR(1) state.
                let lalrParserStateId = Map.find lrParserStateId lrToLalrIdMap

                /// The LALR(1) table entry for this LALR(1) state and lookahead token.
                let entry =
                    // Create LALR(1) actions from the LR(1) actions.
                    let lalrActions = Set.map (lalrAction lrToLalrIdMap) lrActions

                    // If the LALR(1) table already contains an entry for this LALR(1)
                    // state and lookahead token, merge the actions of this LR(1) state
                    // with the existing LALR(1) actions.
                    match Map.tryFind (lalrParserStateId, lookaheadToken) lalrTable with
                    | None ->
                        lalrActions
                    | Some entry ->
                        Set.union entry lalrActions

                // Add/update this entry in the LALR(1) table.
                Map.add (lalrParserStateId, lookaheadToken) entry lalrTable)

        // Create and return the LALR(1) parser table.
        {   Table = lalrTable;
            ParserStateCount = lalrParserStateCount;
            ReductionRulesById = tableGenState.ReductionRulesById; }

