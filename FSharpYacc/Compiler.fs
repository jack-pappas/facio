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
type PrecompilationState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    /// The nonterminals declared by the specification.
    Nonterminals : Set<'Nonterminal>;
    /// The terminals declared by the specification.
    Terminals : Set<'Nonterminal>;
    //
    Productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>;
    //
    TerminalAssociativities : Map<'Terminal, Associativity>;
    //
    PrecedenceGroups : Set<Symbol<'Nonterminal, 'Terminal>> list;
    /// Validation error messages.
    ValidationErrors : string list;
} with
    /// The empty precompilation state.
    static member Empty = {
        Nonterminals = Set.empty;
        Terminals = Set.empty;
        Productions = Map.empty;
        TerminalAssociativities = Map.empty;
        PrecedenceGroups = List.empty;
        ValidationErrors = List.empty; }

/// Validates the given parser specification, and compiles it into the
/// data structures used by the Graham library.
// TODO : The 'options' parameter may not actually be needed here, but we won't know until
// we really implement this function; however, it may be possible (and useful) to augment
// the "standard" validation checks with backend-specific checks, since some backends may not
// support all features.
let precompile (spec : Specification, options : CompilationOptions) : PrecompilationState<_,_> =
    (* TODO :   This function must be modified/rewritten ASAP to use the State workflow, or it'll soon be unreadable! *)

    /// The initial (empty) precompilation state.
    let precompilationState = PrecompilationState<_,_>.Empty

    // The specification must declare at least one nonterminal as a starting nonterminal.
    let precompilationState =
        if Set.isEmpty spec.StartingProductions then
            let msg = "The specification must declare at least one (1) nonterminal \
                        as a starting nonterminal via the %start declaration."
            { precompilationState with
                ValidationErrors = msg :: precompilationState.ValidationErrors; }
        else
            precompilationState

    // TODO : Implement other validation/precompilation steps.
    //
    //

    // Return the final precompilation state.
    precompilationState

/// Creates a PrecedenceSettings record from the precompilation state.
let private precedenceSettings (precompilationState : PrecompilationState<_,_>)
    : PrecedenceSettings<TerminalIdentifier> =


    raise <| System.NotImplementedException "Compiler.precedenceSettings"
    //PrecedenceSettings.Empty    // TEST

/// Compiles a parser specification into a deterministic pushdown automaton (DPDA),
/// then invokes a specified backend to generate code implementing the parser automaton.
let compile (spec : Specification, options : CompilationOptions) : Choice<_,_> =
    // Validate/precompile the specification.
    let precompilationResult = precompile (spec, options)

    // Return the list of error messages if it's non-empty.
    match precompilationResult.ValidationErrors with
    | (_ :: _ as errorMessages) ->
        Choice2Of2 errorMessages
    | [] ->
        // Create the precedence settings (precedence and associativity maps)
        // from the precompilation result.
        let precedenceSettings =
            precedenceSettings precompilationResult

        /// The grammar created from the parser specification.
        let grammar =
            //
            let rawGrammar : Grammar<string, string> = {
                Terminals = precompilationResult.Terminals;
                Nonterminals = precompilationResult.Nonterminals;
                Productions = precompilationResult.Productions; }

            // Augment the grammar.
            Grammar.Augment (rawGrammar, spec.StartingProductions)

        /// The production-rule-id lookup table.
        let productionRuleIds =
            Grammar.ProductionRuleIds grammar

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
        let slr1Table = Slr1.upgrade (grammar, lr0Table', productionRuleIds)        

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
                Lalr1.upgrade (grammar, slr1Table, productionRuleIds, lookaheadSets)
            
            (*  If we reach this point, the grammar is not LALR(1), but we can still create a
                parser by taking certain actions to resolve any remaining conflicts.
                Emit a _warning_ message for each of these conflicts, specifying the action
                we've taken to resolve it. *)
            //
            let lalr1Table' =
                Lr0.resolveConflicts lalr1Table

            // Return the compiled parser table.
            Choice1Of2 lalr1Table'

