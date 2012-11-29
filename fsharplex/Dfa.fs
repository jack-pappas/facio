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

///// Given a DFA which accepts language L, produces an NFA which accepts the reverse of L.
//let reverse (dfa : LexerDfa) : LexerNfa =
//    // Reverse the direction of the edges in the transition map.
//    // OPTIMIZE : This could (and should) easily be optimized to be much more efficient.
//    let transitions =
//        let transitions =
//            LexerDfaGraph.ofVertexSet dfa.Transitions.Vertices
//        (transitions, dfa.Transitions.EdgeSets)
//        ||> Map.fold (fun transitions edgeEndpoints edgeSet ->
//            (transitions, edgeSet)
//            ||> CharSet.fold (fun transitions symbol ->
//                // Reverse the source and target vertices of the edge.
//                LexerDfaGraph.addEdge edgeEndpoints.Target edgeEndpoints.Source symbol transitions))
//
//    // Change the final states to initial states, and vice versa.
//    // TODO
//
//    // Return the resulting NFA.
//    raise <| System.NotImplementedException "Dfa.reverse"
//
///// Minimizes a DFA.
//let minimize (dfa : Dfa) : Dfa =
//    // Minimize the DFA using Brzozowski's algorithm.
//    dfa
//    |> reverse
//    |> ofNfa
//    |> reverse
//    |> ofNfa


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
    Buffer : Queue<'Symbol>;
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
            Buffer = Queue.empty;
            CurrentState = initialState;
            LastFinalState = initialState; }

    /// Marks the current DFA state as the last final DFA state visited
    /// by the tokenizer. This function should only be called when the
    /// current DFA state is a final (accepting) state.
    let markFinalState (tokenizerState : TokenizerState<'Symbol>) =
        (),
        { tokenizerState with
            LastFinalState = tokenizerState.CurrentState; }

    /// Accepts any symbols pending acceptance.
    let acceptPending (tokenizerState : TokenizerState<'Symbol>) =
        (),
        { tokenizerState with
            Accepted =
                // OPTIMIZE : Implement a Queue.fold function to
                // avoid creating the intermediate array.
                (tokenizerState.Accepted, Queue.toArray tokenizerState.Pending)
                ||> Array.fold (fun accepted el -> el :: accepted);
            Pending = Queue.empty; }

    //
    let checkpoint (tokenizerState : TokenizerState<'Symbol>) =
        let (), tokenizerState = markFinalState tokenizerState
        acceptPending tokenizerState

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
        raise <| System.NotImplementedException "TokenizerState.reject"
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
    RuleClause : RuleIdentifier * uint32;
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

(* TODO :   Once 'tokenize' works correctly, modify it so the return type is:
                seq<Choice<Token<'Symbol>, InvalidToken<'Symbol>>>
            This allows the start/end position of the tokens to be returned as well. *)
(*
/// <summary>Tokenizes a sequence of symbols using the specified DFA.</summary>
/// <remarks>
/// This function can be used to unit-test DFAs and lexers without having to
/// generate code for them. It can also be used to test the code-generation
/// functionality; for a given sequence of symbols, a generated/compiled lexer
/// should produce the exact same sequence of tokens produced by this function.
/// </remarks>
let tokenize (dfa : LexerDfa) (symbols : seq<_>) : seq<Choice<int<RegexIndex> * _[], _[]>> =
    //
    let rec tokenize (symbolEnumerator : System.Collections.Generic.IEnumerator<_>) tokenizerState = seq {
        // Try to read a symbol from the stream or pending characters queue.
        let symbol, tokenizerState =
            // If the buffer contains any symbols, return the next symbol in
            // the buffer; otherwise, try to read a character from the symbol stream.
            if Queue.isEmpty tokenizerState.Buffer then
                let symbol =
                    if symbolEnumerator.MoveNext () then
                        Some symbolEnumerator.Current
                    else None

                symbol, tokenizerState
            else
                let symbol, buffer = Queue.dequeue tokenizerState.Buffer
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
                // If the last final DFA state is the initial DFA state and there
                // are some symbols we could still parse, reject the first pending
                // symbol and restart tokenizing.
                if tokenizerState.LastFinalState = dfa.InitialState then
                    if not <| Queue.isEmpty tokenizerState.Pending then
                        let rejectedSymbol, pending = Queue.dequeue tokenizerState.Pending
                        yield Choice2Of2 [| rejectedSymbol |]

                        // Move the remaining pending symbols into the buffer.
                        let tokenizerState =
                            { tokenizerState with
                                Pending = Queue.empty;
                                Buffer = pending; }

                        // Start matching again at the initial DFA state.
                        let (), tokenizerState = TokenizerState.transition dfa.InitialState tokenizerState
                        let (), tokenizerState = TokenizerState.checkpoint tokenizerState
                        yield! tokenize symbolEnumerator tokenizerState
                else
                    // Emit the current token (set at the last-encountered final state).
                    let token, tokenizerState = TokenizerState.accept tokenizerState
                    let regexIndex = Map.find tokenizerState.LastFinalState dfa.FinalStates
                    yield Choice1Of2 (regexIndex, token)

                    // Move the pending symbols into the buffer.
                    // They are placed at the front of the buffer to keep
                    // the symbols in the same order as they were in the symbol stream.
                    let tokenizerState =
                        { tokenizerState with
                            Pending = Queue.empty;
                            Buffer =
                                // OPTIMIZE : Implement a Queue.fold function for this.
                                let buffer = Queue.toArray tokenizerState.Buffer
                                (tokenizerState.Pending, buffer)
                                ||> Array.fold (fun buffer el ->
                                    Queue.enqueue el buffer); }
                    
                    // Start tokenizing again at the initial DFA state.
                    let (), tokenizerState = TokenizerState.transition dfa.InitialState tokenizerState
                    let (), tokenizerState = TokenizerState.markFinalState tokenizerState
                    yield! tokenize symbolEnumerator tokenizerState

        | Some symbol ->
            // Determine if there is a transition out of the current state
            // which is labeled with this symbol.
            let transitionTarget =
                dfa.TransitionsBySymbol
                |> Map.tryFind tokenizerState.CurrentState
                |> Option.bind (Map.tryFind symbol)

            match transitionTarget with
            | Some transitionTarget ->
                // If the current DFA state is a final (accepting) state,
                // mark it as the last final state.
                let (), tokenizerState =
                    if Map.containsKey tokenizerState.CurrentState dfa.FinalStates then
                        let (), tokenizerState = TokenizerState.markFinalState tokenizerState
                        TokenizerState.acceptPending tokenizerState
                    else
                        (), tokenizerState

                // Add this symbol to the queue of pending symbols.
                let (), tokenizerState = TokenizerState.addPending symbol tokenizerState

                // Set the transition target as the current DFA state,
                // then recurse to continue tokenizing.
                let (), tokenizerState = TokenizerState.transition transitionTarget tokenizerState
                yield! tokenize symbolEnumerator tokenizerState

            | None ->
                // If the current DFA state is a final (accepting) state,
                // accept the current token.
                match Map.tryFind tokenizerState.CurrentState dfa.FinalStates with
                | Some regexIndex ->
                    // Add this symbol to the buffer so it will be reprocessed.
                    let tokenizerState =
                        { tokenizerState with
                            Buffer = Queue.enqueue symbol tokenizerState.Buffer; }

                    let (), tokenizerState = TokenizerState.markFinalState tokenizerState   // Is this necessary?
                    let (), tokenizerState = TokenizerState.acceptPending tokenizerState
                    let token, tokenizerState = TokenizerState.accept tokenizerState

                    // Emit the accepted token.
                    yield Choice1Of2 (regexIndex, token)

                    // Start matching again at the initial DFA state.
                    let (), tokenizerState = TokenizerState.transition dfa.InitialState tokenizerState
                    let (), tokenizerState = TokenizerState.markFinalState tokenizerState
                    yield! tokenize symbolEnumerator tokenizerState

                | None ->
                    // If the last final state is the initial state of the DFA, then the current
                    // sequence of characters does not match any of the input Regexes.
                    let token, tokenizerState =
                        if tokenizerState.LastFinalState = dfa.InitialState then
                            if Queue.isEmpty tokenizerState.Pending then
                                // Reject the current symbol and restart tokenizing at the initial DFA state.
                                Choice2Of2 [| symbol |], tokenizerState
                            else
                                // Reject the first symbol in the pending queue.
                                let rejectedSymbol, pending = Queue.dequeue tokenizerState.Pending

                                // Add the current symbol to the pending queue,
                                // which will be merged back into the buffer.
                                let pending = Queue.enqueue symbol pending

                                Choice2Of2 [| rejectedSymbol |],
                                { tokenizerState with
                                    Pending = pending; }
                        else
                            // Add this symbol to the buffer so it will be reprocessed.
                            let tokenizerState =
                                { tokenizerState with
                                    Buffer = Queue.enqueue symbol tokenizerState.Buffer; }

                            // Emit the current token (set at the last-encountered final state).
                            let token, tokenizerState = TokenizerState.accept tokenizerState
                            let regexIndex = Map.find tokenizerState.LastFinalState dfa.FinalStates
                            Choice1Of2 (regexIndex, token), tokenizerState

                    // Emit the token.
                    yield token

                    // Move the pending symbols into the buffer.
                    // They are placed at the front of the buffer to keep
                    // the symbols in the same order as they were in the symbol stream.
                    let tokenizerState =
                        { tokenizerState with
                            Pending = Queue.empty;
                            Buffer =
                                // OPTIMIZE : Implement a Queue.fold function for this.
                                let buffer = Queue.toArray tokenizerState.Buffer
                                (tokenizerState.Pending, buffer)
                                ||> Array.fold (fun buffer el ->
                                    Queue.enqueue el buffer); }
                    
                    // Start tokenizing again at the initial DFA state.
                    let (), tokenizerState = TokenizerState.transition dfa.InitialState tokenizerState
                    let (), tokenizerState = TokenizerState.markFinalState tokenizerState
                    yield! tokenize symbolEnumerator tokenizerState
    }

    // Run the tokenize function.
    TokenizerState.create dfa.InitialState
    |> tokenize (symbols.GetEnumerator ())


/// Produces a sequence containing all words (groups of symbols)
/// in the language accepted by the specified DFA.
/// In many cases, the sequence produced by this function is infinite.
let generate (dfa : LexerDfa) : seq<char[]> =
    //
    raise <| System.NotImplementedException "Dfa.generate"

*)
