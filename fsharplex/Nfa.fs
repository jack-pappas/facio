(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpLex.Nfa

open Graph
open Regex
open Ast


/// NFA state.
[<Measure>] type NfaState
/// Unique identifier for a state within an NFA.
type NfaStateId = int<NfaState>

/// An index into a Regex[] used to create an NFA.
[<Measure>] type RegexIndex

/// A non-deterministic finite automaton (NFA).
type Nfa = {
    /// The initial state of the NFA.
    InitialState : NfaStateId;
    /// The transition graph of the NFA.
    Transitions : LexerNfaGraph<NfaState>;
    /// For each final (accepting) state of the NFA, specifies the index of
    /// the pattern it accepts. The index is the index into the Regex[]
    /// used to create the NFA.
    FinalStates : Map<NfaStateId, int<RegexIndex>>;
}

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private CompileNfa =
    //
    let inline private createState (transitions : LexerNfaGraph<NfaState>) : NfaStateId * _ =
        LexerNfaGraph.createVertex transitions

    //
    let inline private addEpsilonTransition source target (transitions : LexerNfaGraph<NfaState>) =
        let transitions =
            transitions
            |> LexerNfaGraph.addEpsilonEdge source target

        (), transitions

    //
    let inline private addSymbolTransition source target symbol (transitions : LexerNfaGraph<NfaState>) =
        let transitions =
            LexerNfaGraph.addSymbolEdge source target symbol transitions
        (), transitions

    /// Implementation of the algorithm for creating an NFA from a Regex.
    let rec private regexToNfaImpl (regex : Regex<_>) (dest : NfaStateId) (transitions : LexerNfaGraph<NfaState>) cont : NfaStateId * LexerNfaGraph<NfaState> =
        match regex with
        | Regex.Epsilon ->
            let stateId, transitions = createState transitions
            let (), transitions = addEpsilonTransition stateId dest transitions
            cont (stateId, transitions)

        | Regex.Symbol s ->
            let stateId, transitions = createState transitions
            let (), transitions = addSymbolTransition stateId dest s transitions
            cont (stateId, transitions)

        | Alternate (a, b) ->
            let stateId, transitions = createState transitions
            regexToNfaImpl a dest transitions <| fun (aStateId, transitions) ->
                let (), transitions = addEpsilonTransition stateId aStateId transitions
                regexToNfaImpl b dest transitions <| fun (bStateId, transitions) ->
                    let (), transitions = addEpsilonTransition stateId bStateId transitions
                    cont (stateId, transitions)

        | Sequence (a, b) ->
            regexToNfaImpl b dest transitions <| fun (bStateId, transitions) ->
                regexToNfaImpl a bStateId transitions cont

        | ZeroOrMore regex ->
            let stateId, transitions = createState transitions
            let (), transitions = addEpsilonTransition stateId dest transitions
            regexToNfaImpl regex stateId transitions <| fun (starStateId, transitions) ->
                let (), transitions = addEpsilonTransition stateId starStateId transitions
                cont (stateId, transitions)

    /// <summary>Creates an NFA from a Regex.</summary>
    /// <returns>The initial NFA state and the constructed NFA transition graph.</returns>
    let regexToNfa (regex : Regex<_>) (finalState : NfaStateId) (transitions : LexerNfaGraph<NfaState>) : NfaStateId * LexerNfaGraph<NfaState> =
        regexToNfaImpl regex finalState transitions id


/// Compiles multiple Regex instances into a single Nfa.
let ofRegexes (regexes : Regex<_>[]) =
    // Preconditions
    if Array.isEmpty regexes then
        invalidArg "regexes" "Must specify at least one (1) regular expression to be compiled."

    /// The initial NFA state.
    let initialState, transitions =
        LexerNfaGraph.empty
        |> LexerNfaGraph.createVertex
    
    /// Maps final (accepting) NFA states to the index of the Regex they accept.
    let regexFinalStates, regexIndexToFinalState, transitions =
        ((Map.empty<NfaStateId,_>, Map.empty<_,NfaStateId>, transitions), [| 0 .. Array.length regexes - 1 |])
        ||> Array.fold (fun (regexFinalStates, regexIndexToFinalState, transitions) regexIndex ->
            // Add the measure type to the Regex index.
            let regexIndex = LanguagePrimitives.Int32WithMeasure regexIndex

            // Create a final NFA state for this Regex.
            let regexFinalState, transitions =
                LexerNfaGraph.createVertex transitions

            // Add the identifier of the final state to the maps.            
            Map.add regexFinalState regexIndex regexFinalStates,
            Map.add regexIndex regexFinalState regexIndexToFinalState,
            transitions)

    //
    let regexInitialStates, transitions =
        //
        let regexInitialStates = Array.zeroCreate <| Array.length regexes

        //
        let transitions =
            ((transitions, 0<_>), regexes)
            ||> Array.fold (fun (transitions, regexIndex) regex ->
                // Compile the regex.
                let regexInitialState, transitions =
                    /// The final (accepting) NFA state for this Regex.
                    let regexFinalState = Map.find regexIndex regexIndexToFinalState

                    CompileNfa.regexToNfa regex regexFinalState transitions

                // Store the initial NFA state for this Regex.
                regexInitialStates.[int regexIndex] <- regexInitialState

                // Increment the index and continue folding.
                transitions, regexIndex + 1<_>)
            // Discard the counter
            |> fst

        regexInitialStates, transitions

    // Add epsilon-transitions from the initial NFA state (i.e., for the entire NFA)
    // to the initial NFA state for each Regex.
    let transitions =
        (transitions, regexInitialStates)
        ||> Array.fold (fun transitions regexInitialState ->
            LexerNfaGraph.addEpsilonEdge initialState regexInitialState transitions)

    // Create the NFA.
    { InitialState = initialState;
        FinalStates = regexFinalStates;
        Transitions = transitions; }

// TODO : Once 'ofRegexes' is implemented, rewrite this function as a simple wrapper for it.
/// Compiles a Regex into an Nfa.
let ofRegex regex =
    /// The final (accepting) NFA state for the regular expression.
    let finalState, transitions =
        LexerNfaGraph.empty
        |> LexerNfaGraph.createVertex

    /// The final compilation state, containing the completed transition graph of the NFA.
    let initialState, transitions =
        // Compile the regex
        CompileNfa.regexToNfa regex finalState transitions

    // Create an NFA from the final compilation state.
    { InitialState = initialState;
        Transitions = transitions;
        FinalStates =
            Map.empty
            |> Map.add finalState 0<_>; }

