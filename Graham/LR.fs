(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

/// Parser table generators for LR(k) grammars.
namespace Graham.LR

open LanguagePrimitives
open Graham.Grammar
open AugmentedPatterns
open Graham.Analysis
open Graham.Graph


/// An LR(k) item.
type LrItem<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    Nonterminal : 'Nonterminal;
    //
    Production : Symbol<'Nonterminal, 'Terminal>[];
    //
    Position : int<ParserPosition>;
    //
    Lookahead : 'Lookahead;
} with
    /// <inherit />
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
            sprintf ", %A" this.Lookahead
            |> sb.Append |> ignore

        sb.ToString ()

/// An LR(k) parser state -- i.e., a set of LR(k) items.
type LrParserState<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> =
    Set<LrItem<'Nonterminal, 'Terminal, 'Lookahead>>

/// An action which manipulates the state of the
/// parser automaton for an LR(k) parser.
type LrParserAction =
    /// Shift into a state.
    | Shift of ParserStateId
    /// Reduce by a production rule.
    | Reduce of ReductionRuleId
    /// Accept.
    | Accept

    /// <inherit />
    override this.ToString () =
        match this with
        | Shift stateId ->
            "s" + stateId.ToString ()
        | Reduce ruleId ->
            "r" + ruleId.ToString ()
        | Accept ->
            "a"

//
type LrParserConflict =
    //
    | ShiftReduce of ParserStateId * ReductionRuleId
    //
    | ReduceReduce of ReductionRuleId * ReductionRuleId

    /// <inherit />
    override this.ToString () =
        match this with
        | ShiftReduce (shiftStateId, reduceRuleId) ->
            sprintf "s%i/r%i" (int shiftStateId) (int reduceRuleId)
        | ReduceReduce (reduceRuleId1, reduceRuleId2) ->
            sprintf "r%i/r%i" (int reduceRuleId1) (int reduceRuleId2)

//
type LrParserActionSet =
    //
    | Action of LrParserAction
    //
    | Conflict of LrParserConflict

    /// <inherit />
    override this.ToString () =
        match this with
        | Action action ->
            action.ToString ()
        | Conflict conflict ->
            conflict.ToString ()

    /// Creates a new LrParserActionSet with the given action removed;
    /// returns None if the resulting action set would be empty.
    /// No exception is thrown if the set doesn't contain the given action.
    static member Remove action actionSet =
        match actionSet with
        | Action action' ->
            if action = action' then None
            else Some actionSet
        | Conflict conflict ->
            match action, conflict with
            | Shift shiftStateId', ShiftReduce (shiftStateId, reduceRuleId)
                when shiftStateId' = shiftStateId ->
                Some <| Action (Reduce reduceRuleId)
            | Reduce reduceRuleId', ShiftReduce (shiftStateId, reduceRuleId)
                when reduceRuleId' = reduceRuleId ->
                Some <| Action (Shift shiftStateId)
            | Reduce reduceRuleId', ReduceReduce (reduceRuleId1, reduceRuleId2)
                when reduceRuleId' = reduceRuleId1 ->
                Some <| Action (Reduce reduceRuleId2)
            | Reduce reduceRuleId', ReduceReduce (reduceRuleId1, reduceRuleId2)
                when reduceRuleId' = reduceRuleId2 ->
                Some <| Action (Reduce reduceRuleId1)
            | _ ->
                Some actionSet

//
type NonterminalTransition<'Nonterminal
    when 'Nonterminal : comparison> =
    ParserStateId * 'Nonterminal

//
type TerminalTransition<'Terminal
    when 'Terminal : comparison> =
    ParserStateId * 'Terminal

/// LR(k) parser table generation state.
type LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    ParserStateIds : Map<LrParserState<'Nonterminal, 'Terminal, 'Lookahead>, ParserStateId>;
    //
    ParserTransitions : LabeledSparseDigraph<ParserStateId, Symbol<'Nonterminal, 'Terminal>>;
    //
    ActionTable : Map<TerminalTransition<'Terminal>, LrParserActionSet>;
    //
    GotoTable : Map<NonterminalTransition<'Nonterminal>, ParserStateId>;

    (* TODO :   Remove these in favor of using ProductionKey in the LrParserAction.Reduce case. *)
    //
    ReductionRules : Map<'Nonterminal * Symbol<'Nonterminal, 'Terminal>[], ReductionRuleId>;
    //
    ReductionRulesById : Map<ReductionRuleId, 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]>;
}

/// Functions which use the State monad to manipulate an LR(k) table-generation state.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LrTableGenState =
    module Graph = LabeledSparseDigraph

    /// Returns an empty Lr0TableGenState with the given
    /// nonterminal and terminal types.
    let empty : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> = {
        ParserStateIds = Map.empty;
        ParserTransitions = Graph.empty;
        ActionTable = Map.empty;
        GotoTable = Map.empty;
        ReductionRules = Map.empty;
        ReductionRulesById = Map.empty; }

    /// Retrives the identifier for a given parser state (set of items).
    /// If the state has not been assigned an identifier, one is created
    /// and added to the table-generation state before returning.
    let stateId
        (parserState : LrParserState<'Nonterminal, 'Terminal, 'Lookahead>)
        (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        // Try to retrieve an existing id for this state.
        match Map.tryFind parserState tableGenState.ParserStateIds with
        | Some parserStateId ->
            parserStateId, tableGenState

        | None ->
            // Create a new ID for this state.
            let parserStateId =
                tableGenState.ParserStateIds.Count + 1
                |> Int32WithMeasure

            // Return the id, along with the updated table-gen state.
            parserStateId,
            { tableGenState with
                ParserStateIds =
                    Map.add parserState parserStateId tableGenState.ParserStateIds;
                // Add this state to the transition graph's vertex-set.
                ParserTransitions = Graph.addVertex parserStateId tableGenState.ParserTransitions; }

    //
    let reductionRuleId
        (reductionRule : 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[])
        (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        // Reduction rules should only be added, but for safety we'll check to
        // see if the rule has already been assigned an identifier.
        match Map.tryFind reductionRule tableGenState.ReductionRules with
        | Some reductionRuleId ->
            reductionRuleId, tableGenState

        | None ->
            // Create a new ID for this reduction rule.
            let reductionRuleId =
                tableGenState.ReductionRules.Count + 1
                |> Int32WithMeasure

            // Return the id, along with the updated table-gen state.
            reductionRuleId,
            { tableGenState with
                ReductionRules =
                    Map.add reductionRule reductionRuleId tableGenState.ReductionRules;
                ReductionRulesById =
                    Map.add reductionRuleId reductionRule tableGenState.ReductionRulesById; }

    //
    let private impossibleActionSetErrorMsg<'Terminal when 'Terminal : comparison> (sourceState : ParserStateId, transitionSymbol : 'Terminal, entry : LrParserActionSet, action : LrParserAction) =
        sprintf "Cannot add this action because it would create an impossible set of LR(k) parser actions. \
                 (State = %i, Terminal = %A, Existing Entry = %A, New Action = %A)"
                (int sourceState) transitionSymbol entry action

    /// Add a 'shift' action to the parser table.
    let shift (key : TerminalTransition<'Terminal>) targetState
        (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        // Destructure the key to get it's components.
        let sourceState, transitionSymbol = key

        //
        let actionSet =
            match Map.tryFind key tableGenState.ActionTable with
            | None ->
                Action <| Shift targetState
            | Some actionSet ->
                match actionSet with
                | Action (Reduce ruleId) ->
                    Conflict <| ShiftReduce (targetState, ruleId)

                | Action (Shift targetState')
                | Conflict (ShiftReduce (targetState', _))
                    when targetState = targetState' ->
                    // Return the existing action set without modifying it.
                    actionSet

                | entry ->
                    // Adding this action to the existing action set would create
                    // an impossible set of actions, so raise an exception.
                    impossibleActionSetErrorMsg (
                        sourceState, transitionSymbol, entry, Shift targetState)
                    |> invalidOp

        (),
        { tableGenState with
            // Update the table with the new action set.
            ActionTable = Map.add key actionSet tableGenState.ActionTable;
            // Add an edge labeled with this symbol to the transition graph.
            ParserTransitions =
                tableGenState.ParserTransitions
                |> Graph.addEdge sourceState targetState (Symbol.Terminal transitionSymbol); }

    /// Add a 'reduce' action to the ACTION table.
    let reduce (key : TerminalTransition<'Terminal>)
                (reductionRuleId : ReductionRuleId)
                (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        // Destructure the key to get it's components.
        let sourceState, transitionSymbol = key

        //
        let actionSet =
            match Map.tryFind key tableGenState.ActionTable with
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
                    impossibleActionSetErrorMsg (
                        sourceState, transitionSymbol, actionSet, Reduce reductionRuleId)
                    |> invalidOp

        // Update the table with the new action set.
        (),
        { tableGenState with
            ActionTable = Map.add key actionSet tableGenState.ActionTable; }

    /// Add an entry to the GOTO table.
    let goto (key : NonterminalTransition<'Nonterminal>)
                (targetState : ParserStateId)
                (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        // Destructure the key to get it's components.
        let sourceState, transitionSymbol = key

        //
        match Map.tryFind key tableGenState.GotoTable with
        | None ->
            (),
            { tableGenState with
                // Update the table with the new entry.
                GotoTable = Map.add key targetState tableGenState.GotoTable;
                // Add an edge labelled with this symbol to the transition graph.
                ParserTransitions =
                    tableGenState.ParserTransitions
                    |> Graph.addEdge sourceState targetState (Symbol.Nonterminal transitionSymbol); }

        | Some entry ->
            // If the existing entry is the same as the target state,
            // there's nothing to do -- just return the existing 'tableGenState'.
            if entry = targetState then
                (), tableGenState
            else
                let msg = sprintf "Cannot add the entry (g%i) to the GOTO table; \
                                    it already contains an entry (g%i) for the key %A."
                                    (int targetState) (int entry) key
                invalidOp msg

    /// Add an 'accept' action to the parser table.
    let accept (sourceState : ParserStateId) (tableGenState : LrTableGenState<'Nonterminal, AugmentedTerminal<'Terminal>, 'Lookahead>) =
        //
        let key = sourceState, EndOfFile

        //
        let actionSet =
            match Map.tryFind key tableGenState.ActionTable with
            | None ->
                // Create a new 'accept' action for this action set.
                Action Accept
            | Some ((Action Accept) as actionSet) ->
                // The action set doesn't need to be modified.
                actionSet
            | Some actionSet ->
                // Adding an Accept action to the existing action set would create
                // an impossible set of actions, so raise an exception.
                impossibleActionSetErrorMsg (
                    sourceState, EndOfFile, actionSet, Accept)
                |> invalidOp

        // Update the table with the new entry.
        (),
        { tableGenState with
            ActionTable = Map.add key actionSet tableGenState.ActionTable; }


/// LR(k) parser table.
type LrParserTable<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    ParserStates : Map<ParserStateId, LrParserState<'Nonterminal, 'Terminal, 'Lookahead>>;
    //
    ParserTransitions : LabeledSparseDigraph<ParserStateId, Symbol<'Nonterminal, 'Terminal>>;
    //
    ActionTable : Map<TerminalTransition<'Terminal>, LrParserActionSet>;
    //
    GotoTable : Map<NonterminalTransition<'Nonterminal>, ParserStateId>;

    (* TODO :   Remove this in favor of using ProductionKey in the LrParserAction.Reduce case. *)
    //
    ReductionRulesById : Map<ReductionRuleId, 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]>;
} with
    /// Removes an action from the action set corresponding to a specified key.
    static member RemoveAction (table : LrParserTable<'Nonterminal, 'Terminal, 'Lookahead>, key, action) =
        // Try to retrieve the existing action set; if no action set exists for the specified key,
        // return without modifying the table.
        match Map.tryFind key table.ActionTable with
        | None ->
            table
        | Some actionSet ->
            // Remove the action from the action set.
            match LrParserActionSet.Remove action actionSet with
            | Some actionSet' when actionSet = actionSet' ->
                // The action set wasn't modified, so there's no need to modify the parser table.
                table
            | actionSet' ->
                /// The ACTION table updated with the modified action set.
                let actionTable =
                    match actionSet' with
                    | None ->
                        Map.remove key table.ActionTable
                    | Some actionSet' ->
                        Map.add key actionSet' table.ActionTable

                // If the action to be removed is a Shift, then we must also remove
                // the corresponding edge from the ParserTransitions graph.
                let parserTransitions =
                    match action with
                    | Shift targetState ->
                        let sourceState = fst key
                        LabeledSparseDigraph.removeEdge sourceState targetState table.ParserTransitions
                    | _ ->
                        table.ParserTransitions

                // Return the modified parser table.
                { table with
                    ActionTable = actionTable;
                    ParserTransitions = parserTransitions; }

