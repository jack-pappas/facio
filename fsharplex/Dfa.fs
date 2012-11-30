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
open Nfa
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
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal Dfa =
    /// Compute the one-step transition map for a _set_ of NFA states.
    // OPTIMIZE : Once the representation of the NFA transitions is changed to
    // allow faster lookup of out-edges from a state, this function could be
    // rewritten to be much simpler.
    let oneStepTransitions (states : Set<NfaStateId>) (nfa : LexerNfa) =
        let transitionEdges = nfa.Transitions.Edges
        (Map.empty, states)
        ||> Set.fold (fun moves state ->
            (moves, transitionEdges)
            ||> Map.fold (fun moves edgeEndpoints edge ->
                if edgeEndpoints.Source <> state then
                    moves
                else
                    match edge with
                    | Epsilon ->
                        moves
                    | Symbol sym ->
                        let targets =
                            match Map.tryFind sym moves with
                            | None ->
                                Set.singleton edgeEndpoints.Target
                            | Some targets ->
                                Set.add edgeEndpoints.Target targets

                        Map.add sym targets moves))

    // Private, recursive implementation of the epsilon-closure algorithm.
    // Uses a worklist-style algorithm to avoid non-tail-recursive-calls.
    let rec private epsilonClosureImpl (closure : Set<NfaStateId>) (nfa : LexerNfa) (pending : Set<NfaStateId>) =
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
                    ||> Map.fold (fun epsilonTargets edgeEndpoints edge ->
                        if edgeEndpoints.Source <> state then
                            epsilonTargets
                        else
                            match edge with
                            | Symbol _ ->
                                epsilonTargets
                            | Epsilon ->
                                Set.add edgeEndpoints.Target epsilonTargets)

                // Add the targets of any epsilon-transitions to the set of
                // pending states, then recurse to continue processing.
                epsilonTargets
                |> Set.union pending
                |> epsilonClosureImpl closure nfa

    /// Computes the epsilon-closure of a specified NFA state.
    let epsilonClosure (state : NfaStateId) (nfa : LexerNfa) =
        // Call the recursive implementation.
        Set.singleton state
        |> epsilonClosureImpl Set.empty nfa

    //
    type CompilationState = {
        //
        Transitions : LexerDfaGraph<DfaState>;
        /// Maps sets of NFA states to the DFA state representing the set.
        NfaStateSetToDfaState : Map<Set<NfaStateId>, DfaStateId>;
        /// Maps a DFA state to the set of NFA states it represents.
        DfaStateToNfaStateSet : Map<DfaStateId, Set<NfaStateId>>;
    }

    //
    let inline private tryGetDfaState nfaStateSet (compilationState : CompilationState) =
        Map.tryFind nfaStateSet compilationState.NfaStateSetToDfaState

    //
    let inline private getNfaStateSet dfaState (compilationState : CompilationState) =
        Map.find dfaState compilationState.DfaStateToNfaStateSet

    //
    let private createState nfaStateSet (compilationState : CompilationState) =
        // Preconditions
        if Set.isEmpty nfaStateSet then
            invalidArg "nfaStateSet" "A DFA state cannot be created for the empty set of NFA states."

        Debug.Assert (
            not <| Map.containsKey nfaStateSet compilationState.NfaStateSetToDfaState,
            sprintf "The compilation state already contains a DFA state for the NFA state %O." nfaStateSet)

        /// The DFA state representing this set of NFA states.
        let (dfaState : DfaStateId), transitions =
            LexerDfaGraph.createVertex compilationState.Transitions

        // Add the new DFA state to the compilation state.
        let compilationState =
            { compilationState with
                NfaStateSetToDfaState = Map.add nfaStateSet dfaState compilationState.NfaStateSetToDfaState;
                DfaStateToNfaStateSet = Map.add dfaState nfaStateSet compilationState.DfaStateToNfaStateSet;
                Transitions = transitions; }

        // Return the new DFA state and the updated compilation state.
        dfaState, compilationState

    /// The main NFA -> DFA compilation function.
    let rec private compileRec (nfa : LexerNfa) (pending : Set<DfaStateId>) (compilationState : CompilationState) =
        // If there are no more pending states, we're finished compiling the DFA.
        if Set.isEmpty pending then
            compilationState
        else
            //
            let currentState = Set.minElement pending
            let pending = Set.remove currentState pending

            let nfaStateSet = getNfaStateSet currentState compilationState

            //
            let transitionsFromCurrentNfaStateSet =
                oneStepTransitions nfaStateSet nfa
                |> Map.map (fun _ nfaStateSet ->
                    epsilonClosureImpl Set.empty nfa nfaStateSet)

            // For each set of NFA states targeted by a transition,
            // retrieve the corresponding DFA state. If a corresponding
            // DFA state cannot be found, one will be created.
            let transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState =
                ((Map.empty, Set.empty, compilationState), transitionsFromCurrentNfaStateSet)
                ||> Map.fold (fun (transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState) symbol targetNfaStateSet ->
                    let targetDfaState, unvisitedTransitionTargets, compilationState =
                        let maybeDfaState =
                            tryGetDfaState targetNfaStateSet compilationState

                        match maybeDfaState with
                        | Some targetDfaState ->
                            targetDfaState, unvisitedTransitionTargets, compilationState
                        | None ->
                            // Create a DFA state for this set of NFA states.
                            let newDfaState, compilationState = createState targetNfaStateSet compilationState

                            // Add this new DFA state to the set of unvisited states
                            // targeted by transitions from the current DFA state.
                            let unvisitedTransitionTargets =
                                Set.add newDfaState unvisitedTransitionTargets

                            newDfaState,
                            unvisitedTransitionTargets,
                            compilationState

                    //
                    let transitionsFromCurrentDfaState =
                        Map.add symbol targetDfaState transitionsFromCurrentDfaState

                    transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState)

            // Add any newly-created, unvisited states to the
            // set of states which still need to be visited.
            let pending = Set.union pending unvisitedTransitionTargets

            //
            let compilationState =
                { compilationState with
                    Transitions =
                        // Add the unvisited transition targets to the transition graph.
                        (compilationState.Transitions, transitionsFromCurrentDfaState)
                        ||> Map.fold (fun transitions symbol target ->
                            LexerDfaGraph.addEdge currentState target symbol transitions); }

            // Continue processing recursively.
            compileRec nfa pending compilationState

    /// Information about overlapping rule clauses discovered during DFA compilation.
    type internal RuleClauseOverlapInfo = {
        //
        Rule : RuleIdentifier;
        /// The (index of the) clause which will be
        /// accepted by the compiled DFA.
        Accepted : RuleClauseIndex;
        /// The (indices of the) overlapped clauses.
        /// These will never be accepted by the compiled DFA.
        Overlapped : Set<RuleClauseIndex>;
    }

    /// The compiled DFA, plus additional compilation data which may
    /// be useful for diagnostics purposes.
    type internal DfaCompilationResult = {
        /// The compiled DFA.
        Dfa : LexerDfa;
        /// Maps sets of NFA states to the DFA state representing the set.
        NfaStateSetToDfaState : Map<Set<NfaStateId>, DfaStateId>;
        /// Maps a DFA state to the set of NFA states it represents.
        DfaStateToNfaStateSet : Map<DfaStateId, Set<NfaStateId>>;
        /// Information about overlapping Regexes discovered during DFA compilation.
        RegexOverlapInfo : RuleClauseOverlapInfo list;
    }

    //
    let private transitionsBySymbol (transitions : LexerDfaGraph<DfaState>) =
        (Map.empty, transitions.EdgeSets)
        ||> Map.fold (fun transitionsBySymbol edgeEndpoints symbols ->
            let transitionsFromSource =
                let transitionsFromSource = Map.tryFind edgeEndpoints.Source transitionsBySymbol
                defaultArg transitionsFromSource Map.empty

            let transitionsFromSource =
                (transitionsFromSource, symbols)
                ||> CharSet.fold (fun transitionsFromSource symbol ->
                    Map.add symbol edgeEndpoints.Target transitionsFromSource)

            Map.add edgeEndpoints.Source transitionsFromSource transitionsBySymbol)

    //
    let compile (nfa : LexerNfa) : DfaCompilationResult =
        // The initial (empty) compilation state.
        let compilationState : CompilationState = {
            NfaStateSetToDfaState = Map.empty;
            DfaStateToNfaStateSet = Map.empty;
            Transitions = LexerDfaGraph.empty; }

        // The initial DFA state.
        let initialState, compilationState =
            /// The epsilon-closure of the initial NFA state.
            let initialStateEClosure = epsilonClosure nfa.InitialState nfa

            // Create the initial DFA state from the epsilon-closure
            // of the initial NFA state.
            createState initialStateEClosure compilationState

        // Compile the NFA into the DFA.
        let compilationState =
            compileRec nfa (Set.singleton initialState) compilationState

        /// Maps each final (accepting) DFA state to the
        /// (index of) the Regex it accepts.
        let finalStates, regexOverlapInfo =
            // TEMP : Create a map of NFA state -> RuleIdentifier so we can
            // easily determine if an NFA state is a final state, and if so,
            // which rule (not rule clause) it belongs to.
            let nfaFinalStatesToRules =
                (Map.empty, nfa.RuleClauseFinalStates)
                ||> Map.fold (fun nfaFinalStatesToRules ruleId ruleClauseFinalStates ->
                    (nfaFinalStatesToRules, ruleClauseFinalStates)
                    ||> Array.fold (fun nfaFinalStatesToRules nfaStateId ->
                        Map.add nfaStateId ruleId nfaFinalStatesToRules))

            ((Map.empty, []), compilationState.DfaStateToNfaStateSet)
            ||> Map.fold (fun (finalStates, ruleClauseOverlapInfo) dfaState nfaStateSet ->
                /// The NFA states (if any) in the set of NFA states represented
                /// by this DFA state which are final (accepting) states.
                let nfaFinalStateSet =
                    nfaStateSet
                    |> Set.filter (fun nfaState ->
                        Map.containsKey nfaState nfaFinalStatesToRules)
                
                // If any of the NFA states in this DFA state are final (accepting) states,
                // then this DFA state is also an accepting state.
                if Set.isEmpty nfaFinalStateSet then
                    finalStates, ruleClauseOverlapInfo
                else
                    //
                    let ruleId = Map.find (Set.minElement nfaFinalStateSet) nfaFinalStatesToRules

                    /// The (indices of the) rule clauses accepted by this DFA state.
                    let finalStateRuleClauses : Set<RuleClauseIndex> =
                        nfaFinalStateSet
                        |> Set.map (fun nfaState ->
                            nfa.RuleClauseFinalStates
                            |> Map.find ruleId
                            |> Array.findIndex ((=) nfaState)
                            |> LanguagePrimitives.Int32WithMeasure)

                    (* If this DFA state accepts more than one of the input Regexes, it means
                       those Regexes overlap. Since a DFA state can only accept a single Regex,
                       we simply choose the Regex with the lowest-valued index; this convention
                       is a de-facto standard for lexer generators. *)

                    /// The (index of) the rule clause accepted by this DFA state.
                    let acceptedRegex = Set.minElement finalStateRuleClauses

                    // If there was more than one final state, add information about the
                    // overlapped states to 'ruleClauseOverlapInfo'.
                    let ruleClauseOverlapInfo =
                        if Set.count finalStateRuleClauses = 1 then
                            ruleClauseOverlapInfo
                        else
                            let overlapInfo = {
                                Rule = ruleId;
                                Accepted = acceptedRegex;
                                Overlapped = Set.remove acceptedRegex finalStateRuleClauses; }
                            overlapInfo :: ruleClauseOverlapInfo

                    // Add this DFA state and the accepted Regex to the map.
                    Map.add dfaState acceptedRegex finalStates,
                    ruleClauseOverlapInfo)

        // Create the DFA.
        let dfa = {
            Transitions = compilationState.Transitions;
            TransitionsBySymbol = transitionsBySymbol compilationState.Transitions;
            RuleClauseFinalStates = Map.empty;
            RuleInitialStates = Map.empty;
            InitialState = initialState; }

        // Return the DFA along with any data from the final compilation state which
        // does not become part of the DFA; this additional data may be displayed or
        // logged to help diagnose any possible issues with the compiled DFA.
        {   Dfa = dfa;
            NfaStateSetToDfaState = compilationState.NfaStateSetToDfaState;
            DfaStateToNfaStateSet = compilationState.DfaStateToNfaStateSet;
            RegexOverlapInfo = regexOverlapInfo; }


/// Converts an NFA into a DFA.
let ofNfa (nfa : LexerNfa) : LexerDfa =
    // Compile the NFA into a DFA.
    let compilationResult = Dfa.compile nfa
    
    // Return the compiled DFA, discarding any additional data in the result.
    compilationResult.Dfa

////
//let ofNfaWithLog (nfa : LexerNfa) (textWriter : #System.IO.TextWriter) : LexerDfa =
//    // Preconditions
//    if System.Object.ReferenceEquals (null, textWriter) then
//        nullArg "textWriter"
//
//    // Compile the NFA into a DFA.
//    let compilationResult = Dfa.compile nfa
//
//    // Log additional data using the TextWriter.
//    // TODO
//    raise <| System.NotImplementedException "Dfa.ofNfaWithLog"
//
//    // Return the compiled DFA.
//    compilationResult.Dfa
