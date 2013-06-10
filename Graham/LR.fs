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
open Graham
open AugmentedPatterns
open Graham.Analysis
open Graham.Graph


/// Tags an integer as denoting the position of a parser in the right-hand-side (RHS) of a production rule.
[<Measure>] type ParserPositionTag
/// <summary>The position of a parser in the right-hand-side (RHS) of a production rule.</summary>
/// <remarks>
/// The position corresponds to the 0-based index of the next symbol to be parsed,
/// so position values must always be within the range [0, production.Length].
/// </remarks>
type ParserPosition = int<ParserPositionTag>

/// Tags an integer denoting the zero-based index of a parser state
/// within a constructed parser automaton.
[<Measure>] type ParserStateIndexTag
/// The zero-based index of a parser state within a constructed parser automaton.
type ParserStateIndex = int<ParserStateIndexTag>

/// An LR(k) item.
[<DebuggerDisplay("{DebuggerDisplay,nq}")>]
type LrItem<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    ProductionRuleIndex : ProductionRuleIndex;
    //
    Position : ParserPosition;
    //
    Lookahead : 'Lookahead;
} with
    //
    static member CurrentSymbol (item : LrItem<'Nonterminal, 'Terminal, 'Lookahead>)
        (taggedGrammar : TaggedGrammar<'Nonterminal, 'Terminal>) : Symbol<_,_> option =
        // Get the production from the tagged grammar.
        match TagMap.tryFind item.ProductionRuleIndex taggedGrammar.Productions with
        | None ->
            keyNotFound "Cannot find a production with the specified index."
        | Some production ->
            // If the parser position is not at the end of the production,
            // return the next symbol to be parsed.
            let position = int item.Position
            if position < Array.length production then
                Some <| production.[position]
            else None
   
/// An LR(k) parser state -- i.e., a set of LR(k) items.
type LrParserState<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> =
    Set<LrItem<'Nonterminal, 'Terminal, 'Lookahead>>

/// An action which manipulates the state of an LR(k) parser automaton.
type LrParserAction =
    /// Shift into a state.
    | Shift of ParserStateIndex
    /// Reduce by a production rule.
    | Reduce of ProductionRuleIndex
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

/// A conflict between two or more LrParserActions.
/// A deterministic parser cannot be created until all
/// conflicts in its parser table have been resolved.
type LrParserConflictSet = {
    //
    Shift : ParserStateIndex option;
    //
    // Invariant : This set should never be empty.
    Reductions : TagSet<ProductionRuleIndexTag>;
}
with
    /// <inherit />
    override this.ToString () =
        //
        let reductions =
            TagSet.toArray this.Reductions
            |> Array.map (fun productionRuleId ->
                sprintf "r%i" (untag productionRuleId))
            |> String.concat "/"

        // If there's a shift action in this conflict set, prepend it to
        // the string of reduction actions.
        match this.Shift with
        | None ->
            reductions
        | Some shiftStateId ->
            let shift = sprintf "s%i/" (untag shiftStateId)
            shift + reductions

/// A non-empty set of LrParserActions representing the
/// action(s) to take for a specific parser state.
type LrParserActionSet =
    /// A single LrParserAction.
    | Action of LrParserAction
    /// Two (2) conflicting LrParserActions.
    | Conflict of LrParserConflictSet

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
            match action with
            | Shift shiftStateId' ->
                match conflict with
                | { Shift = Some shiftStateId; }
                    when shiftStateId' = shiftStateId ->
                    if TagSet.count conflict.Reductions > 1 then
                        Some <| Conflict { conflict with Shift = None; }
                    else
                        Some <| Action (Reduce <| TagSet.minElement conflict.Reductions)
                | _ ->
                    Some actionSet

            | Reduce reduceRuleId' ->
                let reductions = TagSet.remove reduceRuleId' conflict.Reductions
                if TagSet.isEmpty reductions then
                    match conflict.Shift with
                    | None ->
                        None
                    | Some shiftStateId ->
                        Some <| Action (Shift shiftStateId)
                elif TagSet.count reductions = 1 && Option.isNone conflict.Shift then
                    Some <| Action (Reduce <| TagSet.minElement reductions)
                else
                    Some <| Conflict { conflict with Reductions = reductions; }

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
                match conflict.Shift with
                | None -> false
                | Some shiftStateId ->
                    shiftStateId = shiftStateId'
            | Reduce reduceRuleId' ->
                TagSet.contains reduceRuleId' conflict.Reductions

//
type NonterminalTransition =
    ParserStateIndex * NonterminalIndex

//
type TerminalTransition =
    ParserStateIndex * TerminalIndex

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
    ParserStates : TagBimap<ParserStateIndexTag, LrParserState<'Nonterminal, 'Terminal, 'Lookahead>>;
    //
    ParserTransitions : LabeledSparseDigraph<ParserStateIndex, Symbol<NonterminalIndex, TerminalIndex>>;
    //
    ActionTable : Map<TerminalTransition, LrParserActionSet>;
    //
    GotoTable : Map<NonterminalTransition, ParserStateIndex>;
} with
    /// Private. For use with DebuggerDisplay only.
    /// Gets the number of conflicts in the ACTION table.
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private this.ConflictCount
        with get () =
            this.ActionTable
            |> Map.countWith (fun _ actionSet ->
                match actionSet with
                | Action _ -> false
                | Conflict _ -> true)

    /// Private. For debugging purposes only -- this property can be browsed
    /// in the VS debugger, but it can't be used from within our code.
    member private this.Conflicts
        with get () =
            this.ActionTable
            |> Map.choose (fun _ actionSet ->
                match actionSet with
                | Action _ -> None
                | Conflict conflict ->
                    Some conflict)

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

                        table.ParserTransitions
                        |> LabeledSparseDigraph.removeEdge sourceState targetState
                    | _ ->
                        table.ParserTransitions

                // Return the modified parser table.
                { table with
                    ActionTable = actionTable;
                    ParserTransitions = parserTransitions; }


/// LR(k) parser table generation state.
type LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> =
    LrParserTable<'Nonterminal, 'Terminal, 'Lookahead>

/// Functions which use the State monad to manipulate an LR(k) table-generation state.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LrTableGenState =
    module Graph = LabeledSparseDigraph

    /// Returns an empty LrTableGenState with the given
    /// nonterminal and terminal types.
    let empty<'Nonterminal, 'Terminal, 'Lookahead
        when 'Nonterminal : comparison
        and 'Terminal : comparison
        and 'Lookahead : comparison> : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> =
        {   ParserStates = TagBimap.empty;
            ParserTransitions = Graph.empty;
            ActionTable = Map.empty;
            GotoTable = Map.empty; }

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
        (state : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>)
        : _ * LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> =
        // Try to retrieve an existing id for this state.
        match TagBimap.tryFindValue parserState state.ParserStates with
        | Some parserStateId ->
            (false, parserStateId), state
        | None ->
            // Create a new ID for this state.
            let parserStateId =
                tag <| TagBimap.count state.ParserStates

            // Return the id, along with the updated table-generation state.
            (true, parserStateId),
            { state with
                // Add this state to the transition graph's vertex-set.
                ParserTransitions = Graph.addVertex parserStateId state.ParserTransitions;
                // Add this state (by it's state-id) to the table.
                ParserStates =
                    TagBimap.add parserStateId parserState state.ParserStates; }

    //
    let private impossibleActionSetErrorMsg<'Terminal when 'Terminal : comparison>
        (sourceState : ParserStateIndex, transitionSymbol : 'Terminal, entry : LrParserActionSet, action : LrParserAction) =
        sprintf "Cannot add this action because it would create an impossible set of LR(k) parser actions. \
                 (State = %i, Terminal = %A, Existing Entry = %A, New Action = %A)"
                (int sourceState) transitionSymbol entry action

    /// Add a 'shift' action to the parser table.
    let shift (key : TerminalTransition) targetState
        (state : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>)
        : unit * LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> =
        // Destructure the key to get it's components.
        let sourceState, transitionSymbol = key

        //
        let actionSet =
            match Map.tryFind key state.ActionTable with
            | None ->
                Action <| Shift targetState
            | Some actionSet ->
                match actionSet with
                | Action (Shift targetState')
                | Conflict ({ Shift = Some targetState'; })
                    when targetState = targetState' ->
                    // Return the existing action set without modifying it.
                    actionSet

                | Action (Reduce ruleId) ->
                    Conflict {
                        Shift = Some targetState;
                        Reductions = TagSet.singleton ruleId; }

                | Conflict ({ Shift = None; } as conflict) ->
                    Conflict {
                        conflict with
                            Shift = Some targetState; }

                | entry ->
                    // Adding this action to the existing action set would create
                    // an impossible set of actions, so raise an exception.
                    impossibleActionSetErrorMsg (
                        sourceState, transitionSymbol, entry, Shift targetState)
                    |> invalidOp

        // Update the table-generation state.
        (),
        { state with
            // Update the table with the new action set.
            ActionTable = Map.add key actionSet state.ActionTable;
            // Add an edge labeled with this symbol to the transition graph.
            ParserTransitions =
                state.ParserTransitions
                |> Graph.addEdge sourceState targetState (Symbol.Terminal transitionSymbol); }

    /// Add a 'reduce' action to the ACTION table.
    let reduce (key : TerminalTransition) (productionRuleId : ProductionRuleIndex)
        (state : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>)
        : unit * LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> =
        //
        let actionSet =
            match Map.tryFind key state.ActionTable with
            | None ->
                Action <| Reduce productionRuleId
            | Some actionSet ->
                match actionSet with
                | Action (Shift shiftStateId) ->
                    Conflict {
                        Shift = Some shiftStateId;
                        Reductions = TagSet.singleton productionRuleId; }

                | Action (Reduce productionRuleId') ->
                    Conflict {
                        Shift = None;
                        Reductions =
                            TagSet.empty
                            |> TagSet.add productionRuleId'
                            |> TagSet.add productionRuleId; }

                | Action (Reduce productionRuleId')
                    when productionRuleId = productionRuleId' ->
                    // Return the existing action set without modifying it.
                    actionSet

                | Conflict conflict ->
                    if TagSet.contains productionRuleId conflict.Reductions then
                        // Return the existing action set without modifying it.
                        actionSet
                    else
                        Conflict {
                            conflict with
                                Reductions = TagSet.add productionRuleId conflict.Reductions; }

                | actionSet ->
                    // Destructure the key to get it's components.
                    let sourceState, transitionSymbol = key

                    // Adding this action to the existing action set would create
                    // an impossible set of actions, so raise an exception.
                    impossibleActionSetErrorMsg (
                        sourceState, transitionSymbol, actionSet, Reduce productionRuleId)
                    |> invalidOp

        // Update the table-generation state.
        (),
        { state with
            // Update the table with the new action set.
            ActionTable = Map.add key actionSet state.ActionTable; }

    /// Add an entry to the GOTO table.
    let goto (key : NonterminalTransition) (targetState : ParserStateIndex)
        (state : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>)
        : unit * LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> =
        // Destructure the key to get it's components.
        let sourceState, transitionSymbol = key

        //
        match Map.tryFind key state.GotoTable with
        | None ->
            // Update the table-generation state.
            (),
            { state with
                // Update the table with the new entry.
                GotoTable = Map.add key targetState state.GotoTable;
                // Add an edge labelled with this symbol to the transition graph.
                ParserTransitions =
                    state.ParserTransitions
                    |> Graph.addEdge sourceState targetState (Symbol.Nonterminal transitionSymbol); }

        | Some entry ->
            // If the existing entry is the same as the target state,
            // there's nothing to do -- just return the existing 'tableGenState'.
            if entry = targetState then
                (), state
            else
                let msg = sprintf "Cannot add the entry (g%i) to the GOTO table; \
                                    it already contains an entry (g%i) for the key %A."
                                    (int targetState) (int entry) key
                invalidOp msg

    /// Add an 'accept' action to the ACTION table.
    let accept (sourceState : ParserStateIndex) (taggedGrammar : TaggedAugmentedGrammar<'Nonterminal, 'Terminal>)
        (state : LrTableGenState<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>, 'Lookahead>) =
        /// The transition key for the ACTION table.
        let key =
            let eofIndex = TagBimap.findValue EndOfFile taggedGrammar.Terminals
            sourceState, eofIndex

        //
        let actionSet =
            match Map.tryFind key state.ActionTable with
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
        (),
        { state with
            // Add the new action set into the table.
            ActionTable = Map.add key actionSet state.ActionTable; }
