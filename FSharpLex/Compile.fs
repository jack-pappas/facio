(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpLex.Compile

open System.Diagnostics
open SpecializedCollections
open Graph
open Regex
open Ast


/// DFA compilation state.
[<DebuggerDisplay(
    "States = {Transitions.VertexCount}, \
     Final States = {FinalStates.Count}, \
     Transition Sets = {Transitions.EdgeSetCount}")>]
type private CompilationState = {
    //
    Transitions : LexerDfaGraph;
    /// Final (accepting) DFA states.
    FinalStates : Set<DfaStateId>;
    /// Maps regular vectors to the DFA state representing them.
    RegularVectorToDfaState : Map<RegularVector, DfaStateId>;
    /// Maps a DFA state to the regular vector it represents.
    DfaStateToRegularVector : Map<DfaStateId, RegularVector>;
}

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private CompilationState =
    /// Empty compilation state.
    let empty = {
        Transitions = LexerDfaGraph.empty;
        FinalStates = Set.empty;
        RegularVectorToDfaState = Map.empty;
        DfaStateToRegularVector = Map.empty; }

    //
    let inline tryGetDfaState regVec (compilationState : CompilationState) =
        Map.tryFind regVec compilationState.RegularVectorToDfaState

    //
    let inline getRegularVector dfaState (compilationState : CompilationState) =
        Map.find dfaState compilationState.DfaStateToRegularVector

    //
    let createDfaState regVec (compilationState : CompilationState) =
        // Preconditions
        // TODO

        Debug.Assert (
            not <| Map.containsKey regVec compilationState.RegularVectorToDfaState,
            "The compilation state already contains a DFA state for this regular vector.")

        /// The DFA state representing this regular vector.
        let (dfaState : DfaStateId), transitions =
            LexerDfaGraph.createVertex compilationState.Transitions

        // Add the new DFA state to the compilation state.
        let compilationState =
            { compilationState with
                Transitions = transitions;
                FinalStates =
                    // A regular vector represents a final state iff it is nullable.
                    if RegularVector.isNullable regVec then
                        Set.add dfaState compilationState.FinalStates
                    else
                        compilationState.FinalStates;
                RegularVectorToDfaState =
                    Map.add regVec dfaState compilationState.RegularVectorToDfaState;
                DfaStateToRegularVector =
                    Map.add dfaState regVec compilationState.DfaStateToRegularVector;
                 }

        // Return the new DFA state and the updated compilation state.
        dfaState, compilationState

//
let private transitions regularVector universe (transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState) derivativeClass =
    // Ignore empty derivative classes.
    if CharSet.isEmpty derivativeClass then
        transitionsFromCurrentDfaState,
        unvisitedTransitionTargets,
        compilationState
    else
        // Choose an element from the derivative class; any element
        // will do (which is the point behind the derivative classes).
        let derivativeClassElement = CharSet.minElement derivativeClass

        // The derivative of the regular vector w.r.t. the chosen element.
        let regularVector' =
            regularVector
            // Compute the derivative of the regular vector
            |> RegularVector.derivative derivativeClassElement
            // Canonicalize the derivative vector.
            // THIS IS EXTREMELY IMPORTANT -- this algorithm absolutely
            // will not work without this step.
            |> RegularVector.canonicalize universe

        let targetDfaState, unvisitedTransitionTargets, compilationState =
            let maybeDfaState =
                CompilationState.tryGetDfaState regularVector' compilationState

            match maybeDfaState with
            | Some targetDfaState ->
                targetDfaState,
                unvisitedTransitionTargets,
                compilationState
            | None ->
                // Create a DFA state for this regular vector.
                let newDfaState, compilationState =
                    CompilationState.createDfaState regularVector' compilationState

                // Add this new DFA state to the set of unvisited states
                // targeted by transitions from the current DFA state.
                let unvisitedTransitionTargets =
                    Set.add newDfaState unvisitedTransitionTargets

                newDfaState,
                unvisitedTransitionTargets,
                compilationState

        //
        let transitionsFromCurrentDfaState =
            Map.add derivativeClass targetDfaState transitionsFromCurrentDfaState

        transitionsFromCurrentDfaState,
        unvisitedTransitionTargets,
        compilationState

//
let rec private createDfa universe pending compilationState =
    // If there are no more pending states, we're finished compiling.
    if Set.isEmpty pending then
        compilationState
    else
        //
        let currentState = Set.minElement pending
        let pending = Set.remove currentState pending

        //
        let regularVector = CompilationState.getRegularVector currentState compilationState

        // If this regular vector represents the error state, there's nothing to do
        // for it -- just continue processing the worklist.
        if RegularVector.isEmpty regularVector then
            createDfa universe pending compilationState
        else
            /// The approximate set of derivative classes of the regular vector,
            /// representing transitions out of the DFA state representing it.
            let derivativeClasses = RegularVector.derivativeClasses regularVector universe

            // For each DFA state (regular vector) targeted by a transition (derivative class),
            // add the DFA state to the compilation state (if necessary), then add an edge
            // to the transition graph from this DFA state to the target DFA state.
            let transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState =
                ((Map.empty, Set.empty, compilationState), derivativeClasses)
                ||> Set.fold (transitions regularVector universe)

            // Add any newly-created, unvisited states to the
            // set of states which still need to be visited.
            let pending = Set.union pending unvisitedTransitionTargets

            let compilationState =
                { compilationState with
                    Transitions =
                        // Add the unvisited transition targets to the transition graph.
                        (compilationState.Transitions, transitionsFromCurrentDfaState)
                        ||> Map.fold (fun transitions derivativeClass target ->
                            LexerDfaGraph.addEdges currentState target derivativeClass transitions); }

            // Continue processing recursively.
            createDfa universe pending compilationState


/// A deterministic finite automaton (DFA) implementing a lexer rule.
[<DebuggerDisplay(
    "States = {Transitions.VertexCount}, \
     Transitions = {Transitions.EdgeSetCount}")>]
type LexerRuleDfa = {
    /// The transition graph of the DFA.
    Transitions : LexerDfaGraph;
    //
    RuleClauseFinalStates : DfaStateId[];
    /// The initial state of the DFA.
    InitialState : DfaStateId;
}

//
let (*private*) rulePatternsToDfa (rulePatterns : RegularVector) : LexerRuleDfa =
    // Preconditions
    if Array.isEmpty rulePatterns then
        invalidArg "rulePatterns" "The rule must contain at least one (1) pattern."

    // TODO : Compute the "universe" for this rule pattern.
    let universe = CharSet.empty
    let universe =
        CharSet.empty
        |> CharSet.addRange 'a' 'c'
    //raise <| System.NotImplementedException "rulePatternsToDfa"

    // The initial DFA compilation state.
    let initialDfaStateId, compilationState =
        // Canonicalize the patterns before creating a state for them.
        let rulePatterns = RegularVector.canonicalize universe rulePatterns

        CompilationState.empty
        |> CompilationState.createDfaState rulePatterns

    // Compile the DFA.
    let compilationState =
        let initialPending = Set.singleton initialDfaStateId
        createDfa universe initialPending compilationState

    //
    let ruleAcceptingStates =
        //
        let rulesAcceptedByDfaState =
            // TEST
            (Map.empty, compilationState.FinalStates)
            ||> Set.fold (fun map finalDfaStateId ->
                let acceptedRules : Set<RuleClauseIndex> =
                    // Get the regular vector represented by this DFA state.
                    compilationState.DfaStateToRegularVector
                    |> Map.find finalDfaStateId
                    // Determine which lexer rules are accepted by this regular vector.
                    |> RegularVector.acceptingElementsTagged
                
                Map.add finalDfaStateId acceptedRules map)

        (Map.empty, rulesAcceptedByDfaState)
        ||> Map.fold (fun ruleAcceptingStates finalDfaStateId acceptedRules ->
            Debug.Assert (
                not <| Set.isEmpty acceptedRules,
                sprintf "DFA state '%i' is marked as a final state but does not accept any rules." (int finalDfaStateId))

            (ruleAcceptingStates, acceptedRules)
            ||> Set.fold (fun ruleAcceptingStates acceptedRuleIndex ->
                let acceptingStates =
                    match Map.tryFind acceptedRuleIndex ruleAcceptingStates with
                    | Some acceptingStates ->
                        Set.add finalDfaStateId acceptingStates
                    | None ->
                        Set.singleton finalDfaStateId

                Map.add acceptedRuleIndex acceptingStates ruleAcceptingStates))

    // Create a LexerDfa record from the compiled DFA.
    {   Transitions = compilationState.Transitions;
        RuleClauseFinalStates = Array.empty;    // TODO
        InitialState = initialDfaStateId; }

/// Creates pattern-matching DFAs from the lexer rules.
let lexerSpec (spec : Specification) =
    (*  TODO :  Implement a function which performs a single
                traversal over the lexer rules and implements
                several pieces of functionality:
                -   Validate the rules: look for invalid macros, etc.
                -   Replace uses of macros with the pattern assigned to that macro *)

    // TODO : Once the pre-processing steps are complete,
    // compile the lexer rules into individual DFAs.
    // Use Array.Parallel.map for this to provide better
    // performance for large specifications.

    //
    raise <| System.NotImplementedException "lexerSpec"
    ()
