(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpLex.Dfa

open System.Diagnostics
open SpecializedCollections
open Graph
open Regex
open Ast


/// DFA state.
[<Measure>] type DfaState
/// Unique identifier for a state within a DFA.
type DfaStateId = int<DfaState>

/// A deterministic finite automaton (DFA)
/// implementing a lexer specification.
type LexerDfa = {
    /// The transition graph of the DFA.
    Transitions : LexerDfaGraph<DfaState>;
    /// For a DFA state, maps the out-edges (transitions) from that state
    /// to the state targeted by the transition.
    TransitionsBySymbol : Map<DfaStateId, Map<char, DfaStateId>>;
    //
    RuleClauseFinalStates : Map<RuleIdentifier, DfaStateId[]>;
    //
    RuleInitialStates : Map<RuleIdentifier, DfaStateId>;
    /// The initial state of the DFA.
    InitialState : DfaStateId;
}

//
type private CompilationState = {
    //
    Transitions : LexerDfaGraph<DfaState>;
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
                RegularVectorToDfaState = Map.add regVec dfaState compilationState.RegularVectorToDfaState;
                DfaStateToRegularVector = Map.add dfaState regVec compilationState.DfaStateToRegularVector;
                Transitions = transitions; }

        // Return the new DFA state and the updated compilation state.
        dfaState, compilationState


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

        /// The approximate set of derivative classes of the regular vector,
        /// representing transitions out of the DFA state representing it.
        let derivativeClasses = RegularVector.derivativeClasses regularVector universe

        // For each DFA state (regular vector) targeted by a transition (derivative class),
        // add the DFA state to the compilation state (if necessary), then add an edge
        // to the transition graph from this DFA state to the target DFA state.
        let transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState =
            ((Map.empty, Set.empty, compilationState), derivativeClasses)
            ||> Set.fold (fun (transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState) derivativeClass ->
                Debug.Assert (
                    not <| CharSet.isEmpty derivativeClass,
                    "The derivative class is empty.")

                // Choose an element from the derivative class; any element
                // will do (which is the point behind the derivative classes).
                let derivativeClassElement = CharSet.minElement derivativeClass

                // The derivative of the regular vector w.r.t. the chosen element.
                let regularVector' = RegularVector.derivative derivativeClassElement regularVector

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
                compilationState)

        // Add any newly-created, unvisited states to the
        // set of states which still need to be visited.
        let pending = Set.union pending unvisitedTransitionTargets

        let compilationState =
            { compilationState with
                Transitions =
                    // Add the unvisited transition targets to the transition graph.
                    (compilationState.Transitions, transitionsFromCurrentDfaState)
                    ||> Map.fold (fun transitions symbol target ->
                        LexerDfaGraph.addEdge currentState target symbol transitions); }

        // Continue processing recursively.
        createDfa universe pending compilationState

//
let private rulePatternsToDfa (rulePatterns : RegularVector) : LexerDfa =
    // Preconditions
    if Array.isEmpty rulePatterns then
        invalidArg "rulePatterns" "The rule must contain at least one (1) pattern."

    // TODO : Compute the "universe" for this rule pattern.
    let universe = CharSet.empty
    raise <| System.NotImplementedException "rulePatternsToDfa"

    // The initial DFA compilation state.
    let initialDfaStateId, compilationState =
        CompilationState.empty
        |> CompilationState.createDfaState rulePatterns

    // Compile the DFA.
    let compilationState =
        let initialPending = Set.singleton initialDfaStateId
        createDfa universe initialPending compilationState

    // Create a LexerDfa record from the compiled DFA.
    // TODO
    raise <| System.NotImplementedException "rulePatternsToDfa"

// TEST
/// Creates pattern-matching DFAs from the lexer rules.
let createLexerDFAs (spec : Specification) =
(*  TODO :  Implement a function which performs a single
            traversal over the lexer rules and implements
            several pieces of functionality:
            -   Validate the rules: look for invalid macros, etc.
            -   Replace uses of macros with the pattern assigned to that macro *)

    //
    raise <| System.NotImplementedException "createLexerDfa"

