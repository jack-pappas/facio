(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Nfa

open Graph
open Regex


//
type StateTransition<'Symbol> =
    /// The transition does not consume an input value.
    | Epsilon
    /// The symbol consumed by the transition.
    | Symbol of 'Symbol

    override this.ToString () =
        match this with
        | Epsilon ->
            "\u03f5"
        | Symbol sym ->
            sym.ToString ()


/// NFA state.
[<Measure>] type NfaState
/// Unique identifier for a state within an NFA.
type NfaStateId = int<NfaState>

/// An index into a Regex[] used to create an NFA.
[<Measure>] type RegexIndex

/// A non-deterministic finite automaton (NFA).
type Nfa<'Symbol> = {
    /// The initial state of the NFA.
    InitialState : NfaStateId;
    /// The transition graph of the NFA.
    Transitions : SparseGraph<NfaStateId, StateTransition<'Symbol>>;
    /// For each final (accepting) state of the NFA, specifies the index of
    /// the pattern it accepts. The index is the index into the Regex[]
    /// used to create the NFA.
    FinalStates : Map<NfaStateId, int<RegexIndex>>;
}

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private CompileNfa =
    //
    let private createState (transitions : SparseGraph<NfaStateId, StateTransition<'Symbol>>) =
        let newState =
            Set.count transitions.Vertices
            |> LanguagePrimitives.Int32WithMeasure<_>

        let transitions =
            transitions
            |> SparseGraph.addVertex newState

        newState, transitions

    //
    let private addEpsilonTransition source target (transitions : SparseGraph<NfaStateId, StateTransition<'Symbol>>) =
        let transitions =
            transitions
            |> SparseGraph.addEdge source target StateTransition.Epsilon

        (), transitions

    //
    let private addSymbolTransition source target symbol (transitions : SparseGraph<NfaStateId, StateTransition<'Symbol>>) =
        let transitions =
            transitions
            |> SparseGraph.addEdge source target (StateTransition.Symbol symbol)

        (), transitions

    //
    // OPTIMIZE : Rewrite this function using CPS to avoid the overhead of the stack frames.
    let rec regexToNfa (regex : Regex<'Symbol>) (dest : NfaStateId) (transitions : SparseGraph<NfaStateId, StateTransition<'Symbol>>) : NfaStateId * SparseGraph<NfaStateId, StateTransition<'Symbol>> =
        match regex with
        | Regex.Epsilon ->
            let stateId, transitions = createState transitions
            let (), transitions = addEpsilonTransition stateId dest transitions
            stateId, transitions

        | Regex.Symbol s ->
            let stateId, transitions = createState transitions
            let (), transitions = addSymbolTransition stateId dest s transitions
            stateId, transitions

        | Alternate (a, b) ->
            let stateId, transitions = createState transitions
            let aStateId, transitions = regexToNfa a dest transitions
            let (), transitions = addEpsilonTransition stateId aStateId transitions
            let bStateId, transitions = regexToNfa b dest transitions
            let (), transitions = addEpsilonTransition stateId bStateId transitions
            stateId, transitions

        | Sequence (a, b) ->
            (dest, transitions)
            ||> regexToNfa b
            ||> regexToNfa a

        | ZeroOrMore regex ->
            let stateId, transitions = createState transitions
            let (), transitions = addEpsilonTransition stateId dest transitions
            let starStateId, transitions = regexToNfa regex stateId transitions
            let (), transitions = addEpsilonTransition stateId starStateId transitions
            stateId, transitions


/// Compiles multiple Regex instances into a single Nfa.
let ofRegexes (regexes : Regex<'Symbol>[]) =
    // Preconditions
    if Array.isEmpty regexes then
        invalidArg "regexes" "Must specify at least one (1) regular expression to be compiled."

    // TODO
    raise <| System.NotImplementedException "Nfa.ofRegexes"


// TODO : Once 'ofRegexes' is implemented, rewrite this function as a simple wrapper for it.
/// Compiles a Regex into an Nfa.
let ofRegex (regex : Regex<'Symbol>) =
    /// The final (accepting) NFA state for the regular expression.
    let finalState = 0<_>

    /// The final compilation state, containing the completed transition graph of the NFA.
    let initialState, transitions =
        // Add the vertex for the final NFA state of the regex.
        SparseGraph.empty
        |> SparseGraph.addVertex finalState
        // Compile the regex
        |> CompileNfa.regexToNfa regex finalState

    // Create an NFA from the final compilation state.
    { InitialState = initialState;
        Transitions = transitions;
        FinalStates =
            Map.empty
            |> Map.add finalState 0<_>; }


///// <summary>Removes epsilon-transitions from the NFA, producing a new, simpler NFA.</summary>
///// <remarks>This isn't used for minimization -- it's inefficient and doesn't produce
///// the smallest possible automaton -- but it is useful for visualizing the NFA.</remarks>
//// TODO : This doesn't quite work -- it removes some vertices/edges that shouldn't be removed.
//let removeEpsilonTransitions (nfa : Nfa<'Symbol>) =
//    //
//    let workList = System.Collections.Generic.Queue<_> ()
//    
//    //
//    nfa.Transitions.Edges
//    |> Map.iter (fun (q_i, q_j) edge ->
//        match edge with
//        | StateTransition.Symbol _ -> ()
//        | StateTransition.Epsilon ->
//            workList.Enqueue (q_i, q_j))
//
//    //
//    let mutable transitions = nfa.Transitions
//    let mutable finalStates = nfa.FinalStates
//    while workList.Count > 0 do
//        let q_i, q_j = workList.Dequeue ()
//
//        transitions <-
//            (transitions, transitions.Edges)
//            ||> Map.fold (fun transitions (source, q_k) b ->
//                if source = q_j then
//                    match b with
//                    | StateTransition.Symbol _ -> ()
//                    | StateTransition.Epsilon ->
//                        workList.Enqueue (q_i, q_k)
//
//                    SparseGraph.addEdge q_i q_k b transitions
//
//                else
//                    transitions)
//            |> SparseGraph.removeEdge q_i q_j
//
//        finalStates <-
//            match Map.tryFind q_j finalStates with
//            | None ->
//                finalStates
//            | Some patternIndex ->
//                Map.add q_i patternIndex finalStates
//
//    //
//    let transitions =
//        // Remove unreachable states.
//        (transitions, nfa.Transitions.Vertices)
//        ||> Set.fold (fun transitions state ->
//            if state = nfa.InitialState then
//                transitions
//            elif transitions.Edges |> Map.exists (fun (_, q_i) _ -> q_i = state) then
//                transitions
//            else
//                SparseGraph.removeVertex state transitions)
//
//    // Return the simplified NFA.
//    { InitialState = nfa.InitialState;
//        Transitions = transitions;
//        FinalStates = finalStates; }

