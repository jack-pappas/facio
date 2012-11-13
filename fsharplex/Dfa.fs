(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Dfa

open Graph
open Nfa


/// DFA state.
[<Measure>] type DfaState
/// Unique identifier for a state within a DFA.
type DfaStateId = int<DfaState>

/// A deterministic finite automaton (DFA).
type Dfa<'Symbol> = {
    /// The initial state of the DFA.
    InitialState : DfaStateId;
    /// The transition graph of the DFA.
    Transitions : SparseGraph<DfaStateId, 'Symbol>;
    /// The final (accepting) states of the DFA, corresponding to
    /// the list of regular expressions compiled into the DFA.
    FinalStates : DfaStateId[];
}

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private Dfa =
    /// Compute the one-step transition map for a _set_ of NFA states.
    // OPTIMIZE : Once the representation of the NFA transitions is changed to
    // allow faster lookup of out-edges from a state, this function could be
    // rewritten to be much simpler.
    let private oneStepTransitions (states : Set<NfaStateId>) (nfa : Nfa<'Symbol>) =
        let transitionEdges = nfa.Transitions.Edges
        (Map.empty, states)
        ||> Set.fold (fun moves state ->
            (moves, transitionEdges)
            ||> Map.fold (fun moves (source, target) edge ->
                if source <> state then
                    moves
                else
                    match edge with
                    | StateTransition.Epsilon ->
                        moves
                    | StateTransition.Symbol sym ->
                        let targets =
                            match Map.tryFind sym moves with
                            | None ->
                                Set.singleton target
                            | Some targets ->
                                Set.add target targets

                        Map.add sym targets moves))

    // Private, recursive implementation of the epsilon-closure algorithm.
    // Uses a worklist-style algorithm to avoid non-tail-recursive-calls.
    let rec private epsilonClosureImpl (closure : Set<NfaStateId>) (nfa : Nfa<'Symbol>) (pending : Set<NfaStateId>) =
        // If there are no more pending states, we're finished computing.
        if Set.isEmpty pending then
            closure
        else
            // Get the next state to be processed from the set of pending states.
            let state = Set.minElement pending
            let pending = Set.remove state pending

            // If the state is already in the closure, it doesn't need to
            // be reprocessed -- so continue processing with the next pending element.
            if Set.contains state closure then
                epsilonClosureImpl closure nfa pending
            else
                // Add the current state to the closure.
                let closure = Set.add state closure

                // OPTIMIZE : Change the representation of the transitions in the NFA so that
                // given the state, we can specify a StateTransition and get a Set<NfaStateId> of the
                // targets of the out-edges labeled with that StateTransition.
                let epsilonTargets =
                    (Set.empty, nfa.Transitions.Edges)
                    ||> Map.fold (fun epsilonTargets (source, target) edge ->
                        if source <> state then
                            epsilonTargets
                        else
                            match edge with
                            | StateTransition.Symbol _ ->
                                epsilonTargets
                            | StateTransition.Epsilon ->
                                Set.add target epsilonTargets)

                // Add the targets of any epsilon-transitions to the set of
                // pending states, then recurse to continue processing.
                epsilonTargets
                |> Set.union pending
                |> epsilonClosureImpl closure nfa

    /// Computes the epsilon-closure of a specified NFA state.
    let private epsilonClosure (state : NfaStateId) (nfa : Nfa<'Symbol>) =
        // Call the recursive implementation.
        Set.singleton state
        |> epsilonClosureImpl Set.empty nfa

    //
    type private CompilationState<'Symbol> = {
        //
        Transitions : SparseGraph<DfaStateId, 'Symbol>;
        /// Maps sets of NFA states to the DFA state representing the set.
        NfaStateSets : Map<Set<NfaStateId>, DfaStateId>;
    }

    //
    let private getOrCreateState nfaStateSet (compilationState : CompilationState<'Symbol>) =
        match Map.tryFind nfaStateSet compilationState.NfaStateSets with
        | Some dfaState ->
            dfaState, compilationState
        | None ->
            /// The DFA state representing this set of NFA states.
            let dfaState =
                compilationState.NfaStateSets.Count
                |> LanguagePrimitives.Int32WithMeasure

            // Add the new DFA state to the compilation state.
            let compilationState =
                { compilationState with
                    NfaStateSets = Map.add nfaStateSet dfaState compilationState.NfaStateSets; }

            // Return the new DFA state and the updated compilation state.
            dfaState, compilationState

    //
    let rec private compileRec worklist (compilationState : CompilationState<'Symbol>) =
        match worklist with
        | [] ->
            compilationState
        | current :: worklist ->
            raise <| System.NotImplementedException "Dfa.Dfa.compileRec"

    //
    let rec private subsetConstruction (dStates, marked, dTran) =
        if dStates |> Set.exists (fun T -> not <| Set.contains T marked) then
            
            // Mark 

            // do stuff
            failwith ""

        else
            dStates, dTran


    //
    let compile (nfa : Nfa<'Symbol>) : Dfa<'Symbol> =
        /// The epsilon-closure of the initial NFA state.
        let initialStateEClosure = epsilonClosure nfa.InitialState nfa

        /// The one-step transitions from 'initialStateEClosure'.
        let initialStateEClosureTransitions = oneStepTransitions initialStateEClosure nfa


//        /// The compilation state after compilation is complete.
//        let compilationState =
//            // Create the initial compilation state, then compile the NFA.
//            { Transitions = SparseGraph.empty;
//                NfaStateSets = Map.empty; }
//            |> compileRec [initialStateEClosure]



        raise <| System.NotImplementedException "Dfa.Dfa.compile"
                


//
let ofNfa (nfa : Nfa<'Symbol>) : Dfa<'Symbol> =
    Dfa.compile nfa





