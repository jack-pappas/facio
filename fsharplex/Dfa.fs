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
open Collections
open Graph
open Nfa


/// DFA state.
[<Measure>] type DfaState
/// Unique identifier for a state within a DFA.
type DfaStateId = int<DfaState>

/// A deterministic finite automaton (DFA).
type Dfa<'Symbol when 'Symbol : comparison> = {
    /// The initial state of the DFA.
    InitialState : DfaStateId;
    /// The transition graph of the DFA.
    Transitions : LabeledSparseMultidigraph<DfaStateId, 'Symbol>;
    /// For a DFA state, maps the out-edges (transitions) from that state
    /// to the state targeted by the transition.
    TransitionsBySymbol : Map<DfaStateId, Map<'Symbol, DfaStateId>>;
    /// For each final (accepting) state of the DFA, specifies the index of
    /// the pattern it accepts. The index is the index into the Regex[]
    /// used to create the original NFA.
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
    type CompilationState<'Symbol when 'Symbol : comparison> = {
        //
        Transitions : LabeledSparseMultidigraph<DfaStateId, 'Symbol>;
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

        Debug.Assert (
            not <| Map.containsKey nfaStateSet compilationState.NfaStateSetToDfaState,
            sprintf "The compilation state already contains a DFA state for the NFA state %O." nfaStateSet)

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

    /// The main NFA -> DFA compilation function.
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
                            LabeledSparseMultidigraph.addVertex target transitions)
                        // Add the transition edges to the transition graph.
                        |> Map.fold (fun transitions symbol target ->
                            LabeledSparseMultidigraph.addEdge currentState target symbol transitions)
                        <| transitionsFromCurrentDfaState; }

            // Continue processing recursively.
            compileRec pending nfa compilationState

    /// Information about overlapping Regexes discovered during DFA compilation.
    type internal RegexOverlapInfo = {
        /// The (index of the) Regex which will be
        /// accepted by the compiled DFA.
        Accepted : int<RegexIndex>;
        /// The (indices of the) overlapped Regexes.
        /// These will NOT be accepted by the compiled DFA.
        Overlapped : Set<int<RegexIndex>>;
    }

    /// The compiled DFA, plus additional compilation data which may
    /// be useful for diagnostics purposes.
    type internal DfaCompilationResult<'Symbol when 'Symbol : comparison> = {
        /// The compiled DFA.
        Dfa : Dfa<'Symbol>;
        /// Maps sets of NFA states to the DFA state representing the set.
        NfaStateSetToDfaState : Map<Set<NfaStateId>, DfaStateId>;
        /// Maps a DFA state to the set of NFA states it represents.
        DfaStateToNfaStateSet : Map<DfaStateId, Set<NfaStateId>>;
        /// Information about overlapping Regexes discovered during DFA compilation.
        RegexOverlapInfo : RegexOverlapInfo list;
    }

    //
    let private transitionsBySymbol (transitions : LabeledSparseMultidigraph<DfaStateId, 'Symbol>) =
        (Map.empty, transitions.EdgeSets)
        ||> Map.fold (fun transitionsBySymbol (source, target) symbols ->
            let transitionsFromSource =
                let transitionsFromSource = Map.tryFind source transitionsBySymbol
                defaultArg transitionsFromSource Map.empty

            let transitionsFromSource =
                (transitionsFromSource, symbols)
                ||> Set.fold (fun transitionsFromSource symbol ->
                    Map.add symbol target transitionsFromSource)

            Map.add source transitionsFromSource transitionsBySymbol)

    //
    let compile (nfa : Nfa<'Symbol>) : DfaCompilationResult<'Symbol> =
        // The initial (empty) compilation state.
        let compilationState : CompilationState<'Symbol> = {
            NfaStateSetToDfaState = Map.empty;
            DfaStateToNfaStateSet = Map.empty;
            Transitions = LabeledSparseMultidigraph.empty; }

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
                    |> LabeledSparseMultidigraph.addVertex initialState; }

        // Compile the NFA into the DFA.
        let compilationState =
            compileRec (Set.singleton initialState) nfa compilationState

        /// Maps each final (accepting) DFA state to the
        /// (index of) the Regex it accepts.
        let finalStates, regexOverlapInfo =
            ((Map.empty, []), compilationState.DfaStateToNfaStateSet)
            ||> Map.fold (fun (finalStates, regexOverlapInfo) dfaState nfaStateSet ->
                /// The NFA states (if any) in the set of NFA states represented
                /// by this DFA state which are final (accepting) states.
                let nfaFinalStateSet =
                    nfaStateSet
                    |> Set.filter (fun nfaState ->
                        Map.containsKey nfaState nfa.FinalStates)
                
                // If any of the NFA states in this DFA state are final (accepting) states,
                // then this DFA state is also an accepting state.
                if Set.isEmpty nfaFinalStateSet then
                    finalStates, regexOverlapInfo
                else
                    /// The (indices of the) Regexes accepted by this DFA state.
                    let finalStateInputRegexes =
                        nfaFinalStateSet
                        |> Set.map (fun nfaState ->
                            Map.find nfaState nfa.FinalStates)

                    (* If this DFA state accepts more than one of the input Regexes, it means
                       those Regexes overlap. Since a DFA state can only accept a single Regex,
                       we simply choose the Regex with the lowest-valued index; this convention
                       is a de-facto standard for lexer generators. *)

                    /// The (index of) the Regex accepted by this DFA state.
                    let acceptedRegex = Set.minElement finalStateInputRegexes

                    // If there was more than one final state, add information about the
                    // overlapped states to 'regexOverlapInfo'.
                    let regexOverlapInfo =
                        if Set.count finalStateInputRegexes = 1 then
                            regexOverlapInfo
                        else
                            let overlapInfo = {
                                Accepted = acceptedRegex;
                                Overlapped = Set.remove acceptedRegex finalStateInputRegexes; }
                            overlapInfo :: regexOverlapInfo

                    // Add this DFA state and the accepted Regex to the map.
                    Map.add dfaState acceptedRegex finalStates,
                    regexOverlapInfo)

        // Create the DFA.
        let dfa =
            { InitialState = initialState;
                Transitions = compilationState.Transitions;
                TransitionsBySymbol = transitionsBySymbol compilationState.Transitions;
                FinalStates = finalStates; }

        // Return the DFA along with any data from the final compilation state which
        // does not become part of the DFA; this additional data may be displayed or
        // logged to help diagnose any possible issues with the compiled DFA.
        { Dfa = dfa;
           NfaStateSetToDfaState = compilationState.NfaStateSetToDfaState;
           DfaStateToNfaStateSet = compilationState.DfaStateToNfaStateSet;
           RegexOverlapInfo = regexOverlapInfo; }


/// Converts an NFA into a DFA.
let ofNfa (nfa : Nfa<'Symbol>) : Dfa<'Symbol> =
    // Compile the NFA into a DFA.
    let compilationResult = Dfa.compile nfa
    
    // Return the compiled DFA, discarding any additional data in the result.
    compilationResult.Dfa

//
let ofNfaWithLog (nfa : Nfa<'Symbol>) (textWriter : #System.IO.TextWriter) : Dfa<'Symbol> =
    // Preconditions
    if System.Object.ReferenceEquals (null, textWriter) then
        nullArg "textWriter"

    // Compile the NFA into a DFA.
    let compilationResult = Dfa.compile nfa

    // Log additional data using the TextWriter.
    // TODO
    raise <| System.NotImplementedException "Dfa.ofNfaWithLog"

    // Return the compiled DFA.
    compilationResult.Dfa    

/// Given a DFA which accepts language L, produces an NFA which accepts the reverse of L.
let reverse (dfa : Dfa<'Symbol>) : Nfa<'Symbol> =
    // Reverse the direction of the edges in the transition map.
    // OPTIMIZE : This could (and should) easily be optimized to be much more efficient.
    let transitions =
        let transitions =
            LabeledSparseMultidigraph.ofVertexSet dfa.Transitions.Vertices
        (transitions, dfa.Transitions.EdgeSets)
        ||> Map.fold (fun transitions (source, target) edgeSet ->
            (transitions, edgeSet)
            ||> Set.fold (fun transitions symbol ->
                // Reverse the source and target vertices of the edge.
                LabeledSparseMultidigraph.addEdge target source symbol transitions))

    // Change the final states to initial states, and vice versa.
    // TODO

    // Return the resulting NFA.
    raise <| System.NotImplementedException "Dfa.reverse"

/// Minimizes a DFA.
let minimize (dfa : Dfa<'Symbol>) : Dfa<'Symbol> =
    // Minimize the DFA using Brzozowski's algorithm.
    dfa
    |> reverse
    |> ofNfa
    |> reverse
    |> ofNfa


//
type private TokenizerState<'Symbol> = {
    /// The symbols which have been accepted for the current match.
    /// These are stored in reverse order for efficiency, so the
    /// list must be reversed before returning.
    Accepted : 'Symbol list;
    /// Characters which have been read from the symbol stream
    /// but not yet accepted. This allows the stream to be read
    /// in a forward-only manner.
    Pending : Queue<'Symbol>;
    //
    Buffer : 'Symbol list;
    /// The current DFA state.
    CurrentState : DfaStateId;
    /// The last final DFA state visited by the tokenizer.
    LastFinalState : DfaStateId;
}

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private TokenizerState =
    /// Create a new TokenizerState with the specified initial state.
    let create initialState : TokenizerState<'Symbol> =
        { Accepted = List.empty;
            Pending = Queue.empty;
            Buffer = List.empty;
            CurrentState = initialState;
            LastFinalState = initialState; }

    /// Marks the current DFA state as the last final DFA state visited
    /// by the tokenizer. This function should be called ONLY when the current
    /// DFA state is a final (accepting) state.
    let checkpoint (tokenizerState : TokenizerState<'Symbol>) =
        (),
        { tokenizerState with
            Accepted =
                // OPTIMIZE : Implement a Queue.fold function to
                // avoid creating the intermediate array.
                (tokenizerState.Accepted, Queue.toArray tokenizerState.Pending)
                ||> Array.fold (fun accepted el -> el :: accepted);
            Pending = Queue.empty;
            LastFinalState = tokenizerState.CurrentState; }

    /// Gets the current token ('Symbol[]) and clears the list of
    /// accepted symbols from the tokenizer state.
    let accept (tokenizerState : TokenizerState<'Symbol>) =
        // Create the token from the list of accepted symbols.
        Array.ofList <| List.rev tokenizerState.Accepted,
        // Clear the list of accepted symbols in the tokenizer state.
        { tokenizerState with Accepted = List.empty; }

    //
    let reject (tokenizerState : TokenizerState<'Symbol>) : 'Symbol[] * _ =
        // TODO : Transfer characters from 'Pending' to 'Buffer'
        // TODO
        Array.empty, tokenizerState

    /// Adds a symbol to the queue of symbols pending acceptance.
    let addPending symbol (tokenizerState : TokenizerState<'Symbol>) =
        (),
        { tokenizerState with
            Pending = Queue.enqueue symbol tokenizerState.Pending; }

    /// Sets the current DFA state to the target DFA state.
    let transition targetDfaState (tokenizerState : TokenizerState<'Symbol>) =
        (),
        { tokenizerState with
            CurrentState = targetDfaState; }


//
type Token<'Symbol> = {
    //
    Token : 'Symbol[];
    //
    Regex : int<RegexIndex>;
    //
    StartPosition : uint32;
    //
    EndPosition : uint32;
}

//
type InvalidToken<'Symbol> = {
    //
    Token : 'Symbol[];
    //
    StartPosition : uint32;
    //
    EndPosition : uint32;
}

open System.Collections.Generic

(* TODO :   Once 'tokenize' works correctly, modify it so the return type is:
                seq<Choice<Token<'Symbol>, InvalidToken<'Symbol>>>
            This allows the start/end position of the tokens to be returned as well. *)

/// <summary>Tokenizes a sequence of symbols using the specified DFA.</summary>
/// <remarks>
/// This function can be used to unit-test DFAs and lexers without having to
/// generate code for them. It can also be used to test the code-generation
/// functionality; for a given sequence of symbols, a generated/compiled lexer
/// should produce the exact same sequence of tokens produced by this function.
/// </remarks>
let tokenize (dfa : Dfa<'Symbol>) (symbols : seq<'Symbol>) : seq<Choice<int<RegexIndex> * 'Symbol[], 'Symbol[]>> =
    //
    let rec tokenize (symbolEnumerator : IEnumerator<'Symbol>) tokenizerState = seq {
        // Try to read a symbol from the stream or pending characters queue.
        let symbol, tokenizerState =
            // If the buffer contains any symbols, return the next symbol in
            // the buffer; otherwise, try to read a character from the symbol stream.
            match tokenizerState.Buffer with
            | [] ->
                let symbol =
                    if symbolEnumerator.MoveNext () then
                        Some symbolEnumerator.Current
                    else None

                symbol, tokenizerState

            | symbol :: buffer ->
                Some symbol, { tokenizerState with Buffer = buffer; }

        match symbol with
        | None ->
            // The end of the file has been reached.
            // If the current state is a final (accepting) state,
            // accept the current string; otherwise, reject it.
            match Map.tryFind tokenizerState.CurrentState dfa.FinalStates with
            | Some regexIndex ->
                let (), tokenizerState = TokenizerState.checkpoint tokenizerState
                let token, tokenizerState = TokenizerState.accept tokenizerState

                // Emit the token.
                yield Choice1Of2 (regexIndex, token)

            | None ->
                // If there are any pending symbols, reject the first one and restart tokenizing.
                if not <| Queue.isEmpty tokenizerState.Pending then
                    let rejectedSymbol, pending = Queue.dequeue tokenizerState.Pending
                    yield Choice2Of2 [| rejectedSymbol |]

                    // Move the remaining pending symbols into the buffer.
                    let tokenizerState =
                        { tokenizerState with
                            Pending = Queue.empty;
                            Buffer =
                                List.ofArray <| Queue.toArray pending; }

                    // Start matching again at the initial DFA state.
                    let (), tokenizerState = TokenizerState.transition dfa.InitialState tokenizerState
                    let (), tokenizerState = TokenizerState.checkpoint tokenizerState
                    yield! tokenize symbolEnumerator tokenizerState

        | Some symbol ->
            // Add this symbol to the queue of pending symbols.
            let (), tokenizerState = TokenizerState.addPending symbol tokenizerState

            // Determine if there is a transition out of the current state
            // which is labeled with this symbol.
            let transitionTarget =
                dfa.TransitionsBySymbol
                |> Map.tryFind tokenizerState.CurrentState
                |> Option.bind (Map.tryFind symbol)

            match transitionTarget with
            | None ->
                // If the current DFA state is a final (accepting) state,
                // accept the current token.
                match Map.tryFind tokenizerState.CurrentState dfa.FinalStates with
                | Some regexIndex ->
                    let (), tokenizerState = TokenizerState.checkpoint tokenizerState
                    let token, tokenizerState = TokenizerState.accept tokenizerState

                    // Emit the accepted token.
                    yield Choice1Of2 (regexIndex, token)

                    // Start matching again at the initial DFA state.
                    let (), tokenizerState = TokenizerState.transition dfa.InitialState tokenizerState
                    let (), tokenizerState = TokenizerState.checkpoint tokenizerState
                    yield! tokenize symbolEnumerator tokenizerState

                | None ->
                    // If the last final state is the initial state of the DFA, then the current
                    // sequence of characters does not match any of the input Regexes.
                    // Remove the first character from the 'pending' queue, reject it, then restart tokenizing.
                    let token, tokenizerState =
                        if tokenizerState.LastFinalState = dfa.InitialState then
                            let rejectedSymbol, pending = Queue.dequeue tokenizerState.Pending    
                            let tokenizerState = { tokenizerState with Pending = pending; }
                            
                            Choice2Of2 [| rejectedSymbol |], tokenizerState

                        else
                            // Emit the current token (set at the last-encountered final state).
                            let token, tokenizerState = TokenizerState.accept tokenizerState
                            let regexIndex = Map.find tokenizerState.LastFinalState dfa.FinalStates
                            Choice1Of2 (regexIndex, token), tokenizerState

                    // Emit the token.
                    yield token

                    // Move the pending symbols into the buffer.
                    let tokenizerState =
                        { tokenizerState with
                            Pending = Queue.empty;
                            Buffer =
                                // OPTIMIZE : This should be implemented more efficiently,
                                // perhaps as a Queue.toList function.
                                List.ofArray <| Queue.toArray tokenizerState.Pending; }
                    
                    // Start tokenizing again at the initial DFA state.
                    let (), tokenizerState = TokenizerState.transition dfa.InitialState tokenizerState
                    let (), tokenizerState = TokenizerState.checkpoint tokenizerState
                    yield! tokenize symbolEnumerator tokenizerState

            | Some transitionTarget ->
                // If the current DFA state is a final (accepting) state,
                // mark it as the last final state.
                let (), tokenizerState =
                    if Map.containsKey tokenizerState.CurrentState dfa.FinalStates then
                        TokenizerState.checkpoint tokenizerState
                    else
                        (), tokenizerState

                // Set the transition target as the current DFA state,
                // then recurse to continue tokenizing.
                let (), tokenizerState = TokenizerState.transition transitionTarget tokenizerState
                yield! tokenize symbolEnumerator tokenizerState
    }

    // Run the tokenize function.
    TokenizerState.create dfa.InitialState
    |> tokenize (symbols.GetEnumerator ())


/// Produces a sequence containing all words (groups of symbols)
/// in the language accepted by the specified DFA.
/// In many cases, the sequence produced by this function is infinite.
let generate (dfa : Dfa<'Symbol>) : seq<'Symbol[]> =
    //
    raise <| System.NotImplementedException "Dfa.generate"

