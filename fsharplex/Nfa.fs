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

/// A non-deterministic finite automaton (NFA)
/// implementing a lexer specification.
type LexerNfa = {
    /// The transition graph of the NFA.
    Transitions : LexerNfaGraph<NfaState>;
    /// For each lexer rule, contains an array whose elements
    /// are the initial NFA states of the rule's clauses.
    RuleClauseFinalStates : Map<RuleIdentifier, NfaStateId[]>;
    /// The initial NFA state of each lexer rule.
    RuleInitialStates : Map<RuleIdentifier, NfaStateId>;
    /// The initial state of the NFA.
    InitialState : NfaStateId;
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
    let rec private regexToNfaImpl (regex : Regex) (dest : NfaStateId) (transitions : LexerNfaGraph<NfaState>) cont : NfaStateId * LexerNfaGraph<NfaState> =
        match regex with
        | Regex.Epsilon ->
            let stateId, transitions = createState transitions
            let (), transitions = addEpsilonTransition stateId dest transitions
            cont (stateId, transitions)

        | Regex.CharacterSet s ->
            let stateId, transitions = createState transitions
            //let (), transitions = addSymbolTransition stateId dest s transitions
            cont (stateId, transitions)

        | Regex.Or (a, b) ->
            let stateId, transitions = createState transitions
            regexToNfaImpl a dest transitions <| fun (aStateId, transitions) ->
                let (), transitions = addEpsilonTransition stateId aStateId transitions
                regexToNfaImpl b dest transitions <| fun (bStateId, transitions) ->
                    let (), transitions = addEpsilonTransition stateId bStateId transitions
                    cont (stateId, transitions)

        | Regex.Concat (a, b) ->
            regexToNfaImpl b dest transitions <| fun (bStateId, transitions) ->
                regexToNfaImpl a bStateId transitions cont

        | Regex.Star regex ->
            let stateId, transitions = createState transitions
            let (), transitions = addEpsilonTransition stateId dest transitions
            regexToNfaImpl regex stateId transitions <| fun (starStateId, transitions) ->
                let (), transitions = addEpsilonTransition stateId starStateId transitions
                cont (stateId, transitions)

    /// <summary>Creates an NFA from a Regex.</summary>
    /// <returns>The initial NFA state and the constructed NFA transition graph.</returns>
    let regexToNfa (regex : Regex) (finalState : NfaStateId) (transitions : LexerNfaGraph<NfaState>) : NfaStateId * LexerNfaGraph<NfaState> =
        regexToNfaImpl regex finalState transitions id


/// Compiles a lexer specification into an NFA which implements the lexer.
[<CompiledName("CreateFromSpecification")>]
let ofSpecification (spec : Specification) =
    // Preconditions
    // TODO : Add an assertion to check that the specification is valid;
    // the actual validation procedure should have already taken place before
    // this method is called.

    // TODO : Implement a function which takes the rules and macros and
    // inlines the macros into the rule patterns to produce a new set of rules.
    //

    /// The initial NFA state of the lexer.
    let lexerInitialState, transitions =
        LexerNfaGraph.empty
        |> LexerNfaGraph.createVertex

    //
    let ruleInitialStates, ruleClauseFinalStates, transitions =
        ((Map.empty, Map.empty, transitions), spec.Rules)
        ||> Map.fold (fun (ruleInitialStates, ruleClauseFinalStates, transitions) ruleId ruleClauses ->
            /// The initial NFA state for this rule.
            let ruleInitialState, transitions =
                LexerNfaGraph.createVertex transitions

            // Add the initial rule state to the map.
            let ruleInitialStates = Map.add ruleId ruleInitialState ruleInitialStates

            //
            let ruleClauseFinalStateList, transitions =
                (([], transitions), ruleClauses)
                ||> List.fold (fun (ruleClauseFinalStateList, transitions) ruleClause ->
                    /// The final (accepting) NFA state for this rule clause.
                    let finalRuleClauseState, transitions =
                        LexerNfaGraph.createVertex transitions

                    // Add the rule clause's final state to the list.
                    let ruleClauseFinalStateList = finalRuleClauseState :: ruleClauseFinalStateList

                    // Compile the clause's pattern into the NFA.
                    let ruleClauseInitialState, transitions =
                        CompileNfa.regexToNfa ruleClause.Pattern finalRuleClauseState transitions

                    // Add an epsilon-transition from the rule's initial
                    // NFA state to this clause's initial NFA state.
                    let transitions =
                        LexerNfaGraph.addEpsilonEdge ruleInitialState ruleClauseInitialState transitions

                    ruleClauseFinalStateList,
                    transitions)

            // Add the final states of the rule clauses into the map.
            let ruleClauseFinalStates =
                let finalStates =
                    ruleClauseFinalStateList
                    |> List.rev
                    |> List.toArray

                Map.add ruleId finalStates ruleClauseFinalStates

            ruleInitialStates,
            ruleClauseFinalStates,
            transitions)

    // Add epsilon-transitions from the initial NFA state to
    // the initial state of each lexer rule.
    let transitions =
        (transitions, ruleInitialStates)
        ||> Map.fold (fun transitions _ ruleInitialState ->
            LexerNfaGraph.addEpsilonEdge lexerInitialState ruleInitialState transitions)

    // Create and return the NFA.
    {   Transitions = transitions;
        RuleClauseFinalStates = ruleClauseFinalStates;
        RuleInitialStates = ruleInitialStates;
        InitialState = lexerInitialState; }

