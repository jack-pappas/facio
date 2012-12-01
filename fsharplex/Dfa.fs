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
let inline private tryGetDfaState regVec (compilationState : CompilationState) =
    Map.tryFind regVec compilationState.RegularVectorToDfaState

//
let inline private getRegularVector dfaState (compilationState : CompilationState) =
    Map.find dfaState compilationState.DfaStateToRegularVector

//
let private createState regVec (compilationState : CompilationState) =
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

////
//[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
//module internal Dfa =
//
//    // Private, recursive implementation of the epsilon-closure algorithm.
//    // Uses a worklist-style algorithm to avoid non-tail-recursive-calls.
//    let rec private epsilonClosureImpl (closure : Set<NfaStateId>) (nfa : LexerNfa) (pending : Set<NfaStateId>) =
//        // If there are no more pending states, we're finished computing.
//        if Set.isEmpty pending then
//            closure
//        else
//            // Get the next state to be processed from the set of pending states.
//            let state = Set.minElement pending
//            let pending = Set.remove state pending
//
//            // If the state is already in the closure, it doesn't need to
//            // be reprocessed -- so continue processing with the next pending element.
//            if Set.contains state closure then
//                epsilonClosureImpl closure nfa pending
//            else
//                // Add the current state to the closure.
//                let closure = Set.add state closure
//
//                // OPTIMIZE : Change the representation of the transitions in the NFA so that
//                // given the state, we can specify a StateTransition and get a Set<NfaStateId> of the
//                // targets of the out-edges labeled with that StateTransition.
//                let epsilonTargets =
//                    (Set.empty, nfa.Transitions.Edges)
//                    ||> Map.fold (fun epsilonTargets edgeEndpoints edge ->
//                        if edgeEndpoints.Source <> state then
//                            epsilonTargets
//                        else
//                            match edge with
//                            | Symbol _ ->
//                                epsilonTargets
//                            | Epsilon ->
//                                Set.add edgeEndpoints.Target epsilonTargets)
//
//                // Add the targets of any epsilon-transitions to the set of
//                // pending states, then recurse to continue processing.
//                epsilonTargets
//                |> Set.union pending
//                |> epsilonClosureImpl closure nfa
//
//    /// Computes the epsilon-closure of a specified NFA state.
//    let epsilonClosure (state : NfaStateId) (nfa : LexerNfa) =
//        // Call the recursive implementation.
//        Set.singleton state
//        |> epsilonClosureImpl Set.empty nfa
//
//
//    /// The main NFA -> DFA compilation function.
//    let rec private compileRec (nfa : LexerNfa) (pending : Set<DfaStateId>) (compilationState : CompilationState) =
//        // If there are no more pending states, we're finished compiling the DFA.
//        if Set.isEmpty pending then
//            compilationState
//        else
//            //
//            let currentState = Set.minElement pending
//            let pending = Set.remove currentState pending
//
//            let nfaStateSet = getNfaStateSet currentState compilationState
//
//            //
//            let transitionsFromCurrentNfaStateSet =
//                oneStepTransitions nfaStateSet nfa
//                |> Map.map (fun _ nfaStateSet ->
//                    epsilonClosureImpl Set.empty nfa nfaStateSet)
//
//            // For each set of NFA states targeted by a transition,
//            // retrieve the corresponding DFA state. If a corresponding
//            // DFA state cannot be found, one will be created.
//            let transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState =
//                ((Map.empty, Set.empty, compilationState), transitionsFromCurrentNfaStateSet)
//                ||> Map.fold (fun (transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState) symbol targetNfaStateSet ->
//                    let targetDfaState, unvisitedTransitionTargets, compilationState =
//                        let maybeDfaState =
//                            tryGetDfaState targetNfaStateSet compilationState
//
//                        match maybeDfaState with
//                        | Some targetDfaState ->
//                            targetDfaState, unvisitedTransitionTargets, compilationState
//                        | None ->
//                            // Create a DFA state for this set of NFA states.
//                            let newDfaState, compilationState = createState targetNfaStateSet compilationState
//
//                            // Add this new DFA state to the set of unvisited states
//                            // targeted by transitions from the current DFA state.
//                            let unvisitedTransitionTargets =
//                                Set.add newDfaState unvisitedTransitionTargets
//
//                            newDfaState,
//                            unvisitedTransitionTargets,
//                            compilationState
//
//                    //
//                    let transitionsFromCurrentDfaState =
//                        Map.add symbol targetDfaState transitionsFromCurrentDfaState
//
//                    transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState)
//
//            // Add any newly-created, unvisited states to the
//            // set of states which still need to be visited.
//            let pending = Set.union pending unvisitedTransitionTargets
//
//            //
//            let compilationState =
//                { compilationState with
//                    Transitions =
//                        // Add the unvisited transition targets to the transition graph.
//                        (compilationState.Transitions, transitionsFromCurrentDfaState)
//                        ||> Map.fold (fun transitions symbol target ->
//                            LexerDfaGraph.addEdge currentState target symbol transitions); }
//
//            // Continue processing recursively.
//            compileRec nfa pending compilationState
//
//    /// Information about overlapping rule clauses discovered during DFA compilation.
//    type internal RuleClauseOverlapInfo = {
//        //
//        Rule : RuleIdentifier;
//        /// The (index of the) clause which will be
//        /// accepted by the compiled DFA.
//        Accepted : RuleClauseIndex;
//        /// The (indices of the) overlapped clauses.
//        /// These will never be accepted by the compiled DFA.
//        Overlapped : Set<RuleClauseIndex>;
//    }
//
//    /// The compiled DFA, plus additional compilation data which may
//    /// be useful for diagnostics purposes.
//    type internal DfaCompilationResult = {
//        /// The compiled DFA.
//        Dfa : LexerDfa;
//        /// Maps sets of NFA states to the DFA state representing the set.
//        NfaStateSetToDfaState : Map<Set<NfaStateId>, DfaStateId>;
//        /// Maps a DFA state to the set of NFA states it represents.
//        DfaStateToNfaStateSet : Map<DfaStateId, Set<NfaStateId>>;
//        /// Information about overlapping Regexes discovered during DFA compilation.
//        RegexOverlapInfo : RuleClauseOverlapInfo list;
//    }
//
//    //
//    let private transitionsBySymbol (transitions : LexerDfaGraph<DfaState>) =
//        (Map.empty, transitions.EdgeSets)
//        ||> Map.fold (fun transitionsBySymbol edgeEndpoints symbols ->
//            let transitionsFromSource =
//                let transitionsFromSource = Map.tryFind edgeEndpoints.Source transitionsBySymbol
//                defaultArg transitionsFromSource Map.empty
//
//            let transitionsFromSource =
//                (transitionsFromSource, symbols)
//                ||> CharSet.fold (fun transitionsFromSource symbol ->
//                    Map.add symbol edgeEndpoints.Target transitionsFromSource)
//
//            Map.add edgeEndpoints.Source transitionsFromSource transitionsBySymbol)
//
//    //
//    let compile (nfa : LexerNfa) : DfaCompilationResult =
//        // The initial (empty) compilation state.
//        let compilationState : CompilationState = {
//            NfaStateSetToDfaState = Map.empty;
//            DfaStateToNfaStateSet = Map.empty;
//            Transitions = LexerDfaGraph.empty; }
//
//        // The initial DFA state.
//        let initialState, compilationState =
//            /// The epsilon-closure of the initial NFA state.
//            let initialStateEClosure = epsilonClosure nfa.InitialState nfa
//
//            // Create the initial DFA state from the epsilon-closure
//            // of the initial NFA state.
//            createState initialStateEClosure compilationState
//
//        // Compile the NFA into the DFA.
//        let compilationState =
//            compileRec nfa (Set.singleton initialState) compilationState
//
//        /// Maps each final (accepting) DFA state to the
//        /// (index of) the Regex it accepts.
//        let finalStates, regexOverlapInfo =
//            // TEMP : Create a map of NFA state -> RuleIdentifier so we can
//            // easily determine if an NFA state is a final state, and if so,
//            // which rule (not rule clause) it belongs to.
//            let nfaFinalStatesToRules =
//                (Map.empty, nfa.RuleClauseFinalStates)
//                ||> Map.fold (fun nfaFinalStatesToRules ruleId ruleClauseFinalStates ->
//                    (nfaFinalStatesToRules, ruleClauseFinalStates)
//                    ||> Array.fold (fun nfaFinalStatesToRules nfaStateId ->
//                        Map.add nfaStateId ruleId nfaFinalStatesToRules))
//
//            ((Map.empty, []), compilationState.DfaStateToNfaStateSet)
//            ||> Map.fold (fun (finalStates, ruleClauseOverlapInfo) dfaState nfaStateSet ->
//                /// The NFA states (if any) in the set of NFA states represented
//                /// by this DFA state which are final (accepting) states.
//                let nfaFinalStateSet =
//                    nfaStateSet
//                    |> Set.filter (fun nfaState ->
//                        Map.containsKey nfaState nfaFinalStatesToRules)
//                
//                // If any of the NFA states in this DFA state are final (accepting) states,
//                // then this DFA state is also an accepting state.
//                if Set.isEmpty nfaFinalStateSet then
//                    finalStates, ruleClauseOverlapInfo
//                else
//                    //
//                    let ruleId = Map.find (Set.minElement nfaFinalStateSet) nfaFinalStatesToRules
//
//                    /// The (indices of the) rule clauses accepted by this DFA state.
//                    let finalStateRuleClauses : Set<RuleClauseIndex> =
//                        nfaFinalStateSet
//                        |> Set.map (fun nfaState ->
//                            nfa.RuleClauseFinalStates
//                            |> Map.find ruleId
//                            |> Array.findIndex ((=) nfaState)
//                            |> LanguagePrimitives.Int32WithMeasure)
//
//                    (* If this DFA state accepts more than one of the input Regexes, it means
//                       those Regexes overlap. Since a DFA state can only accept a single Regex,
//                       we simply choose the Regex with the lowest-valued index; this convention
//                       is a de-facto standard for lexer generators. *)
//
//                    /// The (index of) the rule clause accepted by this DFA state.
//                    let acceptedRegex = Set.minElement finalStateRuleClauses
//
//                    // If there was more than one final state, add information about the
//                    // overlapped states to 'ruleClauseOverlapInfo'.
//                    let ruleClauseOverlapInfo =
//                        if Set.count finalStateRuleClauses = 1 then
//                            ruleClauseOverlapInfo
//                        else
//                            let overlapInfo = {
//                                Rule = ruleId;
//                                Accepted = acceptedRegex;
//                                Overlapped = Set.remove acceptedRegex finalStateRuleClauses; }
//                            overlapInfo :: ruleClauseOverlapInfo
//
//                    // Add this DFA state and the accepted Regex to the map.
//                    Map.add dfaState acceptedRegex finalStates,
//                    ruleClauseOverlapInfo)
//
//        // Create the DFA.
//        let dfa = {
//            Transitions = compilationState.Transitions;
//            TransitionsBySymbol = transitionsBySymbol compilationState.Transitions;
//            RuleClauseFinalStates = Map.empty;
//            RuleInitialStates = Map.empty;
//            InitialState = initialState; }
//
//        // Return the DFA along with any data from the final compilation state which
//        // does not become part of the DFA; this additional data may be displayed or
//        // logged to help diagnose any possible issues with the compiled DFA.
//        {   Dfa = dfa;
//            NfaStateSetToDfaState = compilationState.NfaStateSetToDfaState;
//            DfaStateToNfaStateSet = compilationState.DfaStateToNfaStateSet;
//            RegexOverlapInfo = regexOverlapInfo; }
//
//
///// Converts an NFA into a DFA.
//let ofNfa (nfa : LexerNfa) : LexerDfa =
//    // Compile the NFA into a DFA.
//    let compilationResult = Dfa.compile nfa
//    
//    // Return the compiled DFA, discarding any additional data in the result.
//    compilationResult.Dfa
//
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


open Regex

//
let rec private goto dfaStateId derivativeClass universe compilationState =
    // Preconditions (assertions only)
    assert (not <| CharSet.isEmpty derivativeClass)

    // Choose an element from the derivative class; any element
    // will do (which is the point behind the derivative classes).
    let derivativeClassElement = CharSet.minElement derivativeClass

    /// The regular vector represented by this DFA state.
    let regVec = getRegularVector dfaStateId compilationState

    // The derivative of the regular vector w.r.t. the chosen element.
    let regVecDerivative =
        RegularVector.derivative derivativeClassElement regVec

    // If this is an error state, return without doing anything else.
    if RegularVector.isEmpty regVecDerivative then
        compilationState
    else
        //
        let targetDfaStateId, compilationState =
            // Get the existing DFA state for this regular vector, if one exists.
            match tryGetDfaState regVec compilationState with
            | Some targetDfaStateId ->
                targetDfaStateId, compilationState

            | None ->
                // Create a new DFA state to represent this regular vector.
                createState regVec compilationState

        // Add a transition between the input DFA state and the
        // DFA state representing the derivative regular vector.
        let compilationState =
            { compilationState with
                Transitions =
                    LexerDfaGraph.addEdge dfaStateId targetDfaStateId derivativeClass compilationState.Transitions; }

        // Continue building the DFA from the derivative vector state.
        explore regVecDerivative universe compilationState

//
and private explore (regVec : RegularVector) universe compilationState =
    /// The approximate set of derivative classes for this regular vector.
    let derivativeClasses = RegularVector.derivativeClasses regVec universe

    // Fold over the approximate set of derivative classes
    // to compute the transitions from the current state.
    (compilationState, derivativeClasses)
    ||> Set.fold (fun compilationState derivativeClass ->
        goto regVec derivativeClass universe compilationState)

//
let private rulePatternsToDfa (rulePatterns : RegularVector) =
    // Preconditions
    if Array.isEmpty rulePatterns then
        invalidArg "rulePatterns" "The rule must contain at least one (1) pattern."

    // The initial DFA compilation state.
    let initialDfaStateId, compilationState =
        0<_>, ()    // TODO

    // Compile the DFA.
    let compilationState =
        ()

    // Create a LexerDfa record from the compiled DFA.
    // TODO

    raise <| System.NotImplementedException "rulePatternsToDfa"
    ()

// TEST
/// Creates pattern-matching DFAs from the lexer rules.
let createLexerDFAs (spec : Specification) =
(*  TODO :  Implement a function which performs a single
            traversal over the lexer rules and implements
            several pieces of functionality:
            -   Validate the rules: look for invalid macros, etc.
            -   Replace uses of macros with the pattern assigned to that macro
            -   Compute the "universe" of characters used within the lexer. *)

    //
    

    // ruleClauseVector = An array containing the pattern of each lexer rule clause.
    // ruleClauseIndexMap = Maps indicies of the 'ruleClauseVector' to a
    //                      (RuleIdentifier, RuleClauseIndex) identifying the rule clause.
    let ruleClauseVector, ruleClauseIndexMap =
        let ruleClauseList, ruleClauseIndexMap =
            (([], Map.empty), spec.Rules)
            ||> Map.fold (fun (ruleClauseList, ruleClauseIndexMap) ruleId clauses ->
                ((ruleClauseList, ruleClauseIndexMap, 0), clauses)
                ||> List.fold (fun (ruleClauseList, ruleClauseIndexMap, clauseIndex) clause ->
                    let taggedClauseIndex : RuleClauseIndex = LanguagePrimitives.Int32WithMeasure clauseIndex
                    clause.Pattern :: ruleClauseList,
                    Map.add ruleClauseIndexMap.Count (ruleId, taggedClauseIndex) ruleClauseIndexMap,
                    clauseIndex + 1)
                // Discard the clause index
                |> fun (x, y, z) -> x, y)

        /// The total number of rule clauses in the lexer specification.
        let ruleClauseCount = List.length ruleClauseList

        // Reverse the list and convert it into an array.
        List.toArray (List.rev ruleClauseList),
        // Since the list is reversed, we need to perform the
        // equivalent operation on the keys of the map.
        (Map.empty, ruleClauseIndexMap)
        ||> Map.fold (fun reversedMap ruleClauseVectorIndex ruleClauseId ->
            Map.add ((ruleClauseCount - 1) - ruleClauseVectorIndex) ruleClauseId reversedMap)

    // Convert the rule patterns to simple regexes.
    // This vector represents the initial DFA state.
    let ruleClauseVector =
        Array.map ExtendedRegex.ToRegex ruleClauseVector

    // The initial DFA compilation state.
    let initialDfaStateId, compilationState =
        0<_>, ()    // TODO

    // Compile the DFA.
    let compilationState =
        ()

    // Create a LexerDfa record for the compiled DFA.
    // TODO

    raise <| System.NotImplementedException "createLexerDfa"

