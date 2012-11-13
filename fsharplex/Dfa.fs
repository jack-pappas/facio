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
    /// For each final (accepting) state of the DFA, specifies the index of
    /// the pattern it accepts. The index is the index into the Regex[]
    /// used to create the original NFA.s
    FinalStates : Map<DfaStateId, int<RegexIndex>>;
}

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal Dfa =
    /// Compute the one-step transition map for a _set_ of NFA states.
    // OPTIMIZE : Once the representation of the NFA transitions is changed to
    // allow faster lookup of out-edges from a state, this function could be
    // rewritten to be much simpler.
    let oneStepTransitions (states : Set<NfaStateId>) (nfa : Nfa<'Symbol>) =
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
    let epsilonClosure (state : NfaStateId) (nfa : Nfa<'Symbol>) =
        // Call the recursive implementation.
        Set.singleton state
        |> epsilonClosureImpl Set.empty nfa

    //
    type CompilationState<'Symbol> = {
        //
        Transitions : SparseGraph<DfaStateId, 'Symbol>;
        /// Maps sets of NFA states to the DFA state representing the set.
        NfaStateSetToDfaState : Map<Set<NfaStateId>, DfaStateId>;
        /// Maps a DFA state to the set of NFA states it represents.
        DfaStateToNfaStateSet : Map<DfaStateId, Set<NfaStateId>>;
    }

    //
    let private tryGetDfaState nfaStateSet (compilationState : CompilationState<'Symbol>) =
        let dfaState = Map.tryFind nfaStateSet compilationState.NfaStateSetToDfaState
        dfaState, compilationState

    //
    let private getNfaStateSet dfaState (compilationState : CompilationState<'Symbol>) =
        let nfaStateSet = Map.find dfaState compilationState.DfaStateToNfaStateSet
        nfaStateSet, compilationState

    //
    let private createState nfaStateSet (compilationState : CompilationState<'Symbol>) =
        // Preconditions
        if Set.isEmpty nfaStateSet then
            invalidArg "nfaStateSet" "A DFA state cannot be created for the empty set of NFA states."

        /// The DFA state representing this set of NFA states.
        let dfaState : DfaStateId =
            compilationState.NfaStateSetToDfaState.Count
            |> LanguagePrimitives.Int32WithMeasure

        // Add the new DFA state to the compilation state.
        let compilationState =
            { compilationState with
                NfaStateSetToDfaState = Map.add nfaStateSet dfaState compilationState.NfaStateSetToDfaState;
                DfaStateToNfaStateSet = Map.add dfaState nfaStateSet compilationState.DfaStateToNfaStateSet; }

        // Return the new DFA state and the updated compilation state.
        dfaState, compilationState

    //
    let rec private compileRec (pending : Set<DfaStateId>) (nfa : Nfa<'Symbol>) (compilationState : CompilationState<'Symbol>) =
        // If there are no more pending states, we're finished compiling the DFA.
        if Set.isEmpty pending then
            compilationState
        else
            //
            let currentState = Set.minElement pending
            let pending = Set.remove currentState pending

            let nfaStateSet, compilationState = getNfaStateSet currentState compilationState

            //
            let transitionsFromCurrentNfaStateSet =
                oneStepTransitions nfaStateSet nfa
                |> Map.map (fun _ nfaStateSet ->
                    epsilonClosureImpl Set.empty nfa nfaStateSet)

            // For each set of NFA states targeted by a transition,
            // retrieve the corresponding DFA state. If a corresponding
            // DFA state cannot be found, it will be created.
            let transitionsFromCurrentDfaState, compilationState =
                ((Map.empty, compilationState), transitionsFromCurrentNfaStateSet)
                ||> Map.fold (fun (transitionsFromCurrentDfaState, compilationState) symbol targetNfaStateSet ->
                    let targetDfaState, compilationState =
                        let maybeDfaState, compilationState = tryGetDfaState targetNfaStateSet compilationState
                        match maybeDfaState with
                        | Some targetDfaState ->
                            targetDfaState, compilationState
                        | None ->
                            createState targetNfaStateSet compilationState

                    //
                    let transitionsFromCurrentDfaState =
                        Map.add symbol targetDfaState transitionsFromCurrentDfaState

                    transitionsFromCurrentDfaState, compilationState)

            // Find DFA states which are transition targets which have not yet
            // been added to the transition graph.
            let unvisitedTransitionTargets =
                let vertices = compilationState.Transitions.Vertices
                (Set.empty, transitionsFromCurrentDfaState)
                ||> Map.fold (fun unvisitedTransitionTargets _ target ->
                    if Set.contains target vertices then
                        unvisitedTransitionTargets
                    else
                        Set.add target unvisitedTransitionTargets)

            //
            let pending = Set.union pending unvisitedTransitionTargets

            //
            let compilationState =
                { compilationState with
                    Transitions =
                        // Add the unvisited transition targets to the transition graph.
                        (compilationState.Transitions, unvisitedTransitionTargets)
                        ||> Set.fold (fun transitions target ->
                            SparseGraph.addVertex target transitions)
                        // Add the transition edges to the transition graph.
                        |> Map.fold (fun transitions symbol target ->
                            SparseGraph.addEdge currentState target symbol transitions)
                        <| transitionsFromCurrentDfaState; }

            // Continue processing recursively.
            compileRec pending nfa compilationState

    //
    type internal DfaCompilationResult<'Symbol> = {
        //
        Dfa : Dfa<'Symbol>;
        /// Maps sets of NFA states to the DFA state representing the set.
        NfaStateSetToDfaState : Map<Set<NfaStateId>, DfaStateId>;
        /// Maps a DFA state to the set of NFA states it represents.
        DfaStateToNfaStateSet : Map<DfaStateId, Set<NfaStateId>>;
    }

    //
    let compile (nfa : Nfa<'Symbol>) : DfaCompilationResult<'Symbol> =
        // The initial (empty) compilation state.
        let compilationState : CompilationState<'Symbol> = {
            NfaStateSetToDfaState = Map.empty;
            DfaStateToNfaStateSet = Map.empty;
            Transitions = SparseGraph.empty; }

        // The initial DFA state.
        let initialState, compilationState =
            /// The epsilon-closure of the initial NFA state.
            let initialStateEClosure = epsilonClosure nfa.InitialState nfa

            // Create the initial DFA state from the epsilon-closure
            // of the initial NFA state.
            createState initialStateEClosure compilationState

        // Add the initial DFA state to the transition graph.
        let compilationState =
            { compilationState with
                Transitions =
                    compilationState.Transitions
                    |> SparseGraph.addVertex initialState; }

        // Compile the NFA into the DFA.
        let compilationState =
            compileRec (Set.singleton initialState) nfa compilationState

        /// Maps each final (accepting) DFA state to the
        /// (index of) the Regex it accepts.
        let finalStates =
            (Map.empty, compilationState.DfaStateToNfaStateSet)
            ||> Map.fold (fun finalStates dfaState nfaStateSet ->
                /// The NFA states (if any) in the set of NFA states represented
                /// by this DFA state which are final (accepting) states.
                let nfaFinalStateSet =
                    nfaStateSet
                    |> Set.filter (fun nfaState ->
                        Map.containsKey nfaState nfa.FinalStates)
                
                // If any of the NFA states in this DFA state are final (accepting) states,
                // then this DFA state is also an accepting state.
                if Set.isEmpty nfaFinalStateSet then
                    finalStates
                else
                    (* TODO :   Determine if it's possible for one DFA state to contain two or
                                more NFA states which are accepting states for different input
                                Regexes. If so, we'll need to tweak the DFA (or perhaps, the DFA
                                compilation algorithm) to handle this correctly. *)
                    let finalStateInputRegexes =
                        nfaFinalStateSet
                        |> Set.map (fun nfaState ->
                            Map.find nfaState nfa.FinalStates)

                    Debug.Assert (
                        Set.count finalStateInputRegexes = 1,
                        "The DFA state contains multiple final (accepting) NFA states accepting \
                        different regular expressions.")

                    /// The (index of) the Regex accepted by the NFA states
                    /// (and therefore, this DFA state).
                    let acceptedRegex = Set.minElement finalStateInputRegexes

                    // Add this DFA state and the accepted Regex to the map.
                    Map.add dfaState acceptedRegex finalStates)

        // Create the DFA.
        let dfa =
            { InitialState = initialState;
                Transitions = compilationState.Transitions;
                FinalStates = finalStates; }

        // DEBUG : Correctness checks on the compiled DFA.
        Debug.Assert (
            not <| Map.isEmpty dfa.FinalStates,
            "The final DFA compilation state does not contain any final (accepting) states.")

        // Return the DFA along with any data from the final compilation state which
        // does not become part of the DFA; this additional data may be displayed or
        // logged to help diagnose any possible issues with the compiled DFA.
        { Dfa = dfa;
           NfaStateSetToDfaState = compilationState.NfaStateSetToDfaState;
           DfaStateToNfaStateSet = compilationState.DfaStateToNfaStateSet; }


//
let ofNfa (nfa : Nfa<'Symbol>) : Dfa<'Symbol> =
    // Compile the NFA into a DFA.
    let compilationResult = Dfa.compile nfa
    
    // Return the compiled DFA, discarding any additional data in the result.
    compilationResult.Dfa


(* TODO :   Implement an 'ofNfaWithLog' function which is similar to 'ofNfa'
            but takes an additional parameter (e.g., a TextWriter) which it
            will use to log additional compilation information before returning
            the compiled DFA. *)


