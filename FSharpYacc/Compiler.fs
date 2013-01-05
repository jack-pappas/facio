(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.Compiler

open Graham.Grammar
open Graham.LR
open FSharpYacc.Ast


//
type ValidationState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    /// The nonterminals declared by the specification.
    Nonterminals : Set<'Nonterminal>;
    /// The terminals declared by the specification.
    Terminals : Set<'Nonterminal>;
    /// Validation error messages.
    ValidationErrors : string list;
} with
    /// The empty validation state.
    static member Empty = {
        Nonterminals = Set.empty;
        Terminals = Set.empty;
        ValidationErrors = List.empty; }

/// Validates the given compiler specification.
// TODO : The 'options' parameter may not actually be needed here, but we won't know until
// we really implement this function; however, it may be possible (and useful) to augment
// the "standard" validation checks with backend-specific checks, since some backends may not
// support all features.
let validate (spec : Specification, options : CompilationOptions) : ValidationState<_,_> =
    (* TODO :   This function must be modified/rewritten ASAP to use the State workflow, or it'll soon be unreadable! *)

    /// The initial (empty) validation state.
    let validationState = ValidationState<_,_>.Empty

    // The specification must declare at least one nonterminal as a starting nonterminal.
    if Set.isEmpty spec.StartingProductions then
        let msg = "The specification must declare at least one (1) nonterminal \
                    as a starting nonterminal via the %start declaration."
        { validationState with
            ValidationErrors = msg :: validationState.ValidationErrors; }
    else
        validationState

/// <summary>Creates the precedence and associativity maps from the specification.</summary>
/// <returns>On success, the rule precedence map, terminal precedence map, and terminal
/// associativity map; on failure, a list of error messages.</returns>
let private precedenceSettings (spec : Specification)
    : PrecedenceSettings<TerminalIdentifier> =
    (* TODO :   Rewrite this function once the ExtCore library is finished.
                We'll be able to implement this function with greater accuracy
                and less work using the workflows it provides. *)

    raise <| System.NotImplementedException "Compiler.precedenceAndAssociativity"

//
let private grammar (spec : Specification) : Grammar<string, string> =
    //
    raise <| System.NotImplementedException "Compiler.grammar"

/// Compiles a parser specification into a deterministic pushdown automaton (DPDA),
/// then invokes a specified backend to generate code implementing the parser automaton.
let compile (spec : Specification, options : CompilationOptions) : Choice<_,_> =
    // Validate the specification.
    let validationResult = validate (spec, options)

    // Return the list of error messages if it's non-empty.
    match validationResult.ValidationErrors with
    | (_ :: _ as errorMessages) ->
        Choice2Of2 errorMessages
    | [] ->
        // Create the precedence settings (precedence and associativity maps) from the specification.
        let precedenceSettings = precedenceSettings spec

        /// The grammar created from the parser specification.
        let grammar =
            // Create a Graham.Grammar from the specification.
            let grammar = grammar spec

            // Augment the grammar.
            Grammar.Augment (grammar, spec.StartingProductions)

        (*  Create the LR(0) automaton from the grammar; report the number of states and
            the number of S/R and R/R conflicts. If there are any conflicts, apply the
            precedence table to the constructed parser table to (possibly) resolve some
            of them. At this point, if there aren't any remaining conflicts, report that
            the grammar is LR(0) and return. *)
        //
        let lr0Table = Lr0.createTable grammar

        /// The LR(0) parser table, after applying precedence settings.
        let lr0Table' =
            // Apply precedences to resolve conflicts.
            Lr0.applyPrecedence (lr0Table, precedenceSettings)

        (*  Upgrade the LR(0) automaton to SLR(1); report the remaining number of S/R and
            R/R conflicts. If there aren't any remaining conflicts, report that the grammar
            is SLR(1) and return. *)
        //
        let slr1Table = Slr1.upgrade (grammar, lr0Table')        

        (*  Upgrade the LR(0)/SLR(1) automaton to LALR(1); report the remaining number of
            S/R and R/R conflicts. If there aren't any remaining conflicts, report that the
            grammar is LALR(1) and return. *)
        //
        let lalrLookaheadSets =
            Lalr1.lookaheadSets (grammar, slr1Table)

        // If we detected that the grammar is not LR(k), stop and return an error message.
        match Lalr1.lookaheadSets (grammar, slr1Table) with
        | Choice2Of2 errorMessage ->
            Choice2Of2 [errorMessage]
        | Choice1Of2 lookaheadSets ->
            //
            let lalr1Table =
                Lalr1.upgrade (grammar, slr1Table, lookaheadSets)
            
            (*  If we reach this point, the grammar is not LALR(1), but we can still create a
                parser by taking certain actions to resolve any remaining conflicts.
                Emit a _warning_ message for each of these conflicts, specifying the action
                we've taken to resolve it. *)
            //
            let lalr1Table' =
                Lr0.resolveConflicts lalr1Table

            // Return the compiled parser table.
            Choice1Of2 lalr1Table'

