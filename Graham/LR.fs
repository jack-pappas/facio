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


//
module private LrItemHelper =
    //
    let compareArrays<'T when 'T : comparison> (arr1 : 'T[], arr2 : 'T[]) : int =
        let len = arr1.Length
        match compare len arr2.Length with
        | 0 ->
            let mutable result = 0
            let mutable idx = 0

            while idx < len && result = 0 do
                result <- compare arr1.[idx] arr2.[idx]
                idx <- idx + 1

            result

        | c -> c

/// An LR(k) item.
[<DebuggerDisplay("{DebuggerDisplay,nq}")>]
[<CustomEquality; CustomComparison>]
type LrItem<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    Nonterminal : 'Nonterminal;
    //
    Production : Symbol<'Nonterminal, 'Terminal>[];
    //
    Lookahead : 'Lookahead;
    //
    Position : int<ParserPosition>;
} with
    /// Private. Only for use with DebuggerDisplayAttribute.
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private this.DebuggerDisplay
        with get () =
            this.ToString '\u2022'

    //
    member this.CurrentSymbol
        with get () =
            let position = int this.Position
            if position = Array.length this.Production then None
            else Some this.Production.[position]

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
    override this.Equals other =
        match other with
        | :? LrItem<'Nonterminal, 'Terminal, 'Lookahead> as other ->
            LrItem.Equals (this, other)
        | _ ->
            false

    /// <inherit />
    override this.GetHashCode () =
        ((19 +
          ((hash this.Nonterminal) <<< 1) + 631) +
          ((hash this.Lookahead) <<< 1) + 631) +
          ((int this.Position) <<< 1) + 631

    /// <inherit />
    override this.ToString () =
        this.ToString '.'

    //
    static member private Equals (item1 : LrItem<'Nonterminal, 'Terminal, 'Lookahead>, item2 : LrItem<'Nonterminal, 'Terminal, 'Lookahead>) =
        item1 === item2 || (
            (box item1.Nonterminal === box item2.Nonterminal || item1.Nonterminal = item2.Nonterminal) &&
            (item1.Production === item2.Production || item1.Production = item2.Production) &&
            (box item1.Lookahead === box item2.Lookahead || item1.Lookahead = item2.Lookahead) &&
            item1.Position = item2.Position)

    interface System.IEquatable<LrItem<'Nonterminal, 'Terminal, 'Lookahead>> with
        member this.Equals other =
            LrItem.Equals (this, other)

    interface System.IComparable with
        member this.CompareTo other =
            match other with
            | :? LrItem<'Nonterminal, 'Terminal, 'Lookahead> as other ->
                // Are the instances actually the same instance?
                if this === other then 0
                else
                    // Are the nonterminals the same or equal?
                    match
                        if box this.Nonterminal === box other.Nonterminal then 0
                        else compare this.Nonterminal other.Nonterminal with
                    | 0 ->
                        // Are the productions the same or equal?
                        match
                            if this.Production === other.Production then 0
                            else LrItemHelper.compareArrays (this.Production, other.Production) with
                        | 0 ->
                            // Are the lookaheads the same or equal?
                            match
                                if box this.Lookahead === box other.Production then 0
                                else compare this.Lookahead other.Lookahead with
                            | 0 ->
                                // Compare the parser positions.
                                compare this.Position other.Position
                            | c -> c
                        | c -> c
                    | c -> c

            | _ ->
                invalidArg "other" "The other object is not a type-compatible instance of LrItem."

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

/// A conflict between two or more LrParserActions.
/// A deterministic parser cannot be created until all
/// conflicts in its parser table have been resolved.
type LrParserConflictSet = {
    //
    Shift : ParserStateId option;
    //
    // Invariant : This set should never be empty.
    Reductions : TagSet<ProductionRuleIdentifier>;
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
            this.ActionTable
            |> Map.countWith (fun _ actionSet ->
                match actionSet with
                | Action _ -> false
                | Conflict _ -> true)

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


//
type LrTableGenEnvironment<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    //
    ProductionRuleIds : Map<'Nonterminal * Symbol<'Nonterminal, 'Terminal>[], ProductionRuleId>;
} with
    /// Creates a new LR(k) parser table generation environment from
    /// a grammar's production rules.
    static member Create (productionRules : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) =
        /// The production-rule-id lookup table.
        let productionRuleIds =
            (Map.empty, productionRules)
            ||> Map.fold (fun productionRuleIds nonterminal rules ->
                (productionRuleIds, rules)
                ||> Array.fold (fun productionRuleIds ruleRhs ->
                    /// The identifier for this production rule.
                    let productionRuleId : ProductionRuleId =
                        tag productionRuleIds.Count

                    // Add this identifier to the map.
                    Map.add (nonterminal, ruleRhs) productionRuleId productionRuleIds))

        // Create and return the environment.
        { ProductionRuleIds = productionRuleIds; }


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
        (sourceState : ParserStateId, transitionSymbol : 'Terminal, entry : LrParserActionSet, action : LrParserAction) =
        sprintf "Cannot add this action because it would create an impossible set of LR(k) parser actions. \
                 (State = %i, Terminal = %A, Existing Entry = %A, New Action = %A)"
                (int sourceState) transitionSymbol entry action

    /// Add a 'shift' action to the parser table.
    let shift (key : TerminalTransition<'Terminal>) targetState
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
    let reduce (key : TerminalTransition<'Terminal>) (productionRuleId : ProductionRuleId)
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
    let goto (key : NonterminalTransition<'Nonterminal>) (targetState : ParserStateId)
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
    let accept (sourceState : ParserStateId)
        (state : LrTableGenState<'Nonterminal, AugmentedTerminal<'Terminal>, 'Lookahead>) =
        /// The transition key for the ACTION table.
        let key = sourceState, EndOfFile

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
