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

/// Parser table generators for LR(k) grammars.
namespace Graham.LR

open System.Diagnostics
open ExtCore
open ExtCore.Collections
open Graham.Grammar
open AugmentedPatterns
open Graham.Analysis
open Graham.Graph


/// An LR(k) item.
[<DebuggerDisplay("{DebuggerDisplay,nq}")>]
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
    /// Private. Only for use with DebuggerDisplayAttribute.
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private this.DebuggerDisplay
        with get () =
            this.ToString '\u2022'

    /// <summary>Private ToString implementation which allows the 'dot' character to be specified.</summary>
    /// <param name="dotChar">The character to use to represent the 'dot' (parser position).</param>
    member private this.ToString (dotChar : char) =
        let sb = System.Text.StringBuilder ()

        // Add the nonterminal text and arrow to the StringBuilder.
        sprintf "%O \u2192" this.Nonterminal
        |> sb.Append |> ignore

        // Is this an empty (epsilon) production?
        if Array.isEmpty this.Production then
            sb.Append " (Empty)" |> ignore
        else
            for i = 0 to Array.length this.Production do
                // Append a space before each symbol.
                sb.Append " " |> ignore

                if i < int this.Position then
                    this.Production.[i].ToString ()
                    |> sb.Append |> ignore
                elif i = int this.Position then
                    // Append the dot character representing the parser position.
                    sb.Append dotChar |> ignore
                else
                    this.Production.[i - 1].ToString ()
                    |> sb.Append |> ignore

        // Append the lookahead symbol, if applicable.
        if typeof<'Lookahead> <> typeof<unit> then
            sprintf ", %A" this.Lookahead
            |> sb.Append |> ignore

        // Return the constructed string.
        sb.ToString ()

    /// <inherit />
    override this.ToString () =
        this.ToString '.'

/// An LR(k) parser state -- i.e., a set of LR(k) items.
type LrParserState<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> =
    Set<LrItem<'Nonterminal, 'Terminal, 'Lookahead>>

/// An action which manipulates the state of an LR(k) parser automaton.
type LrParserAction =
    /// Shift into a state.
    | Shift of ParserStateId
    /// Reduce by a production rule.
    | Reduce of ProductionRuleId
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

/// A conflict between two LrParserActions.
/// A deterministic parser cannot be created until all
/// conflicts in its parser table have been resolved.
type LrParserConflict =
    /// A conflict between a Shift action and a Reduce action.
    | ShiftReduce of ParserStateId * ProductionRuleId
    /// <summary>A conflict between two Reduce actions.</summary>
    | ReduceReduce of ProductionRuleId * ProductionRuleId

    /// <inherit />
    override this.ToString () =
        match this with
        | ShiftReduce (shiftStateId, productionRuleId) ->
            sprintf "s%i/r%i" (Tag.toInt shiftStateId) (Tag.toInt productionRuleId)
        | ReduceReduce (productionRuleId1, productionRuleId2) ->
            sprintf "r%i/r%i" (Tag.toInt productionRuleId1) (Tag.toInt productionRuleId2)

/// A non-empty set of LrParserActions representing the
/// action(s) to take for a specific parser state.
type LrParserActionSet =
    /// A single LrParserAction.
    | Action of LrParserAction
    /// Two (2) conflicting LrParserActions.
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

    /// Determines if an LrParserActionSet contains the specified action.
    static member Contains action actionSet =
        match actionSet with
        | Action action' ->
            action = action'
        | Conflict conflict ->
            match action with
            | Accept -> false
            | Shift shiftStateId' ->
                match conflict with
                | ShiftReduce (shiftStateId, _) ->
                    shiftStateId' = shiftStateId
                | ReduceReduce (_,_) ->
                    false
            | Reduce reduceRuleId' ->
                match conflict with
                | ShiftReduce (_, reduceRuleId) ->
                    reduceRuleId' = reduceRuleId
                | ReduceReduce (reduceRuleId1, reduceRuleId2) ->
                    reduceRuleId' = reduceRuleId1
                    || reduceRuleId' = reduceRuleId2

//
type NonterminalTransition<'Nonterminal
    when 'Nonterminal : comparison> =
    ParserStateId * 'Nonterminal

//
type TerminalTransition<'Terminal
    when 'Terminal : comparison> =
    ParserStateId * 'Terminal

/// LR(k) parser table.
[<DebuggerDisplay("States = {ParserStates.Count,nq}, \
                   Gotos = {GotoTable.Count,nq}, \
                   Actions = {ActionTable.Count,nq}, \
                   Conflicts = {ConflictCount,nq}")>]
type LrParserTable<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    ParserStates : TagBimap<ParserStateIdentifier, LrParserState<'Nonterminal, 'Terminal, 'Lookahead>>;
    //
    ParserTransitions : LabeledSparseDigraph<ParserStateId, Symbol<'Nonterminal, 'Terminal>>;
    //
    ActionTable : Map<TerminalTransition<'Terminal>, LrParserActionSet>;
    //
    GotoTable : Map<NonterminalTransition<'Nonterminal>, ParserStateId>;
} with
    /// Private. For use with DebuggerDisplay only.
    /// Gets the number of conflicts in the ACTION table.
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private this.ConflictCount
        with get () =
            (0, this.ActionTable)
            ||> Map.fold (fun conflictCount _ actionSet ->
                match actionSet with
                | Action _ ->
                    conflictCount
                | Conflict _ ->
                    conflictCount + 1)

    /// Private. For debugging purposes only -- this property can be browsed
    /// in the VS debugger, but it can't be used from within our code.
    member private this.ReduceStates
        with get () =
            (Map.empty, this.ParserStates)
            ||> TagBimap.fold (fun reduceStates stateId items ->
                (reduceStates, items)
                ||> Set.fold (fun reduceStates item ->
                    if int item.Position = Array.length item.Production then
                        let nonterms =
                            match Map.tryFind stateId reduceStates with
                            | None -> Set.singleton item.Nonterminal
                            | Some nonterms ->
                                Set.add item.Nonterminal nonterms
                        Map.add stateId nonterms reduceStates
                    else
                        reduceStates))

    /// Private. For debugging purposes only -- this property can be browsed
    /// in the VS debugger, but it can't be used from within our code.
    member private this.Conflicts
        with get () =
            (Map.empty, this.ActionTable)
            ||> Map.fold (fun conflicts key actionSet ->
                match actionSet with
                | Action _ -> conflicts
                | Conflict conflict ->
                    Map.add key conflict conflicts)

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

//
type LrTableGenEnvironment<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    ParserStateIds : Map<LrParserState<'Nonterminal, 'Terminal, 'Lookahead>, ParserStateId>;
    //
    ProductionRuleIds : Map<'Nonterminal * Symbol<'Nonterminal, 'Terminal>[], ProductionRuleId>;
}

/// LR(k) parser table generation state.
type LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> =
    (*  The table generation state is the table itself plus an "environment" record
        which holds lookup tables only needed while creating the table. *)
    LrTableGenEnvironment<'Nonterminal, 'Terminal, 'Lookahead> *
    LrParserTable<'Nonterminal, 'Terminal, 'Lookahead>

/// Functions which use the State monad to manipulate an LR(k) table-generation state.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LrTableGenState =
    module Graph = LabeledSparseDigraph

    /// Returns an empty LrTableGenState with the given
    /// nonterminal and terminal types.
    let empty : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> =
        // The empty table-gen environment.
        {   ParserStateIds = Map.empty;
            ProductionRuleIds = Map.empty; },
        // The empty parser table.
        {   ParserStates = TagBimap.empty;
            ParserTransitions = Graph.empty;
            ActionTable = Map.empty;
            GotoTable = Map.empty; }

    /// Creates the production-rule-id lookup table from the production rules of a grammar,
    /// then stores it in the environment component of the table-generation state.
    let setProductionRules (productionRules : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>)
                            (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        // Destructure the table-generation state to get it's components.
        let env, table = tableGenState

        /// The production-rule-id lookup table.
        let productionRuleIds =
            (Map.empty, productionRules)
            ||> Map.fold (fun productionRuleIds nonterminal rules ->
                (productionRuleIds, rules)
                ||> Array.fold (fun productionRuleIds ruleRhs ->
                    /// The identifier for this production rule.
                    let productionRuleId : ProductionRuleId =
                        Tag.ofInt productionRuleIds.Count

                    // Add this identifier to the map.
                    Map.add (nonterminal, ruleRhs) productionRuleId productionRuleIds))

        // Update the table-generation state.
        let tableGenState =
            { env with
                ProductionRuleIds = productionRuleIds;
            }, table

        // Return the updated table-generation state.
        (), tableGenState

    /// <summary>Retrives the identifier for a given parser state (set of items).
    /// If the state has not been assigned an identifier, one is created
    /// and added to the table-generation state before returning.</summary>
    /// <returns>
    /// <component>
    ///     <component>true if a new identifier was created for the parser state; otherwise, false.</component>
    ///     <component>The identifier for the parser state.</component>
    /// </component>
    /// <component>The (possibly updated) table-generation state.</component>
    /// </returns>
    let stateId
        (parserState : LrParserState<'Nonterminal, 'Terminal, 'Lookahead>)
        (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>)
        : _ * LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> =
        // Destructure the table-generation state to get it's components.
        let env, table = tableGenState

        // Try to retrieve an existing id for this state.
        match Map.tryFind parserState env.ParserStateIds with
        | Some parserStateId ->
            (false, parserStateId), tableGenState
        | None ->
            // Create a new ID for this state.
            let parserStateId =
                Tag.ofInt env.ParserStateIds.Count

            // Update the table-generation state.
            let tableGenState =
                { env with
                    // Add the new state-id into the table-gen environment.
                    ParserStateIds =
                        Map.add parserState parserStateId env.ParserStateIds; },
                { table with
                    // Add this state to the transition graph's vertex-set.
                    ParserTransitions = Graph.addVertex parserStateId table.ParserTransitions;
                    // Add this state (by it's state-id) to the table.
                    ParserStates =
                        TagBimap.add parserStateId parserState table.ParserStates; }

            // Return the id, along with the updated table-generation state.
            (true, parserStateId), tableGenState

    //
    let private impossibleActionSetErrorMsg<'Terminal when 'Terminal : comparison> (sourceState : ParserStateId, transitionSymbol : 'Terminal, entry : LrParserActionSet, action : LrParserAction) =
        sprintf "Cannot add this action because it would create an impossible set of LR(k) parser actions. \
                 (State = %i, Terminal = %A, Existing Entry = %A, New Action = %A)"
                (int sourceState) transitionSymbol entry action

    /// Add a 'shift' action to the parser table.
    let shift (key : TerminalTransition<'Terminal>) targetState
        (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>)
        : unit * LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> =
        // Destructure the key to get it's components.
        let sourceState, transitionSymbol = key
        // Destructure the table-generation state to get it's components.
        let env, table = tableGenState

        //
        let actionSet =
            match Map.tryFind key table.ActionTable with
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

        // Update the table-generation state.
        let tableGenState =
            env,
            { table with
                // Update the table with the new action set.
                ActionTable = Map.add key actionSet table.ActionTable;
                // Add an edge labeled with this symbol to the transition graph.
                ParserTransitions =
                    table.ParserTransitions
                    |> Graph.addEdge sourceState targetState (Symbol.Terminal transitionSymbol); }
            
        // Return the updated table-generation state.
        (), tableGenState

    /// Add a 'reduce' action to the ACTION table.
    let reduce (key : TerminalTransition<'Terminal>)
                (productionRuleId : ProductionRuleId)
                (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>)
        : unit * LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> =
        // Destructure the key to get it's components.
        let sourceState, transitionSymbol = key
        // Destructure the table-generation state to get it's components.
        let env, table = tableGenState

        //
        let actionSet =
            match Map.tryFind key table.ActionTable with
            | None ->
                Action <| Reduce productionRuleId
            | Some actionSet ->
                match actionSet with
                | Action (Shift shiftStateId) ->
                    Conflict <| ShiftReduce (shiftStateId, productionRuleId)

                | Action (Reduce productionRuleId')
                | Conflict (ShiftReduce (_, productionRuleId'))
                | Conflict (ReduceReduce (productionRuleId', _))
                | Conflict (ReduceReduce (_, productionRuleId'))
                    when productionRuleId = productionRuleId' ->
                    // Return the existing action set without modifying it.
                    actionSet

                | actionSet ->
                    // Adding this action to the existing action set would create
                    // an impossible set of actions, so raise an exception.
                    impossibleActionSetErrorMsg (
                        sourceState, transitionSymbol, actionSet, Reduce productionRuleId)
                    |> invalidOp

        // Update the table-generation state.
        let tableGenState =
            env,
            { table with
                // Update the table with the new action set.
                ActionTable = Map.add key actionSet table.ActionTable; }
        
        // Return the updated table-generation state.
        (), tableGenState            

    /// Add an entry to the GOTO table.
    let goto (key : NonterminalTransition<'Nonterminal>)
                (targetState : ParserStateId)
                (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>)
        : unit * LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> =
        // Destructure the key to get it's components.
        let sourceState, transitionSymbol = key
        // Destructure the table-generation state to get it's components.
        let env, table = tableGenState

        //
        match Map.tryFind key table.GotoTable with
        | None ->
            // Update the table-generation state.
            let tableGenState =
                env,
                { table with
                    // Update the table with the new entry.
                    GotoTable = Map.add key targetState table.GotoTable;
                    // Add an edge labelled with this symbol to the transition graph.
                    ParserTransitions =
                        table.ParserTransitions
                        |> Graph.addEdge sourceState targetState (Symbol.Nonterminal transitionSymbol); }

            // Return the updated table-generation state.
            (), tableGenState                

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

    /// Add an 'accept' action to the ACTION table.
    let accept (sourceState : ParserStateId) (tableGenState : LrTableGenState<'Nonterminal, AugmentedTerminal<'Terminal>, 'Lookahead>) =
        /// The transition key for the ACTION table.
        let key = sourceState, EndOfFile
        // Destructure the table-generation state to get it's components.
        let env, table = tableGenState

        //
        let actionSet =
            match Map.tryFind key table.ActionTable with
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

        // Update the table-generation state.
        let tableGenState =
            env,
            { table with
                // Add the new action set into the table.
                ActionTable = Map.add key actionSet table.ActionTable; }

        // Return the updated table-generation state.
        (), tableGenState

