(*

Copyright 2012-2013 Jack Pappas

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

//
module FSharpYacc.Compiler

open ExtCore
open ExtCore.Collections
open ExtCore.Control
open ExtCore.Control.Collections
open Graham.Grammar
open Graham.LR
open FSharpYacc.Ast


//
type ValidationMessages = {
    //
    Errors : string list;
    //
    Warnings : string list;
}

//
type ProcessedProductionRule<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    //
    Symbols : Symbol<'Nonterminal, 'Terminal>[];
    /// A semantic action to be executed when this rule is matched.
    Action : CodeFragment option;
}

//
type ProcessedSpecification<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    //
    Header : CodeFragment option;
    /// The nonterminals declared by the specification, and their declared type (if provided).
    Nonterminals : Map<'Nonterminal, DeclaredType option>;
    /// The terminals declared by the specification, and their declared type (if provided).
    Terminals : Map<'Terminal, DeclaredType option>;
    //
    ProductionRules : Map<'Nonterminal, ProcessedProductionRule<'Nonterminal, 'Terminal>[]>;
    //
    TerminalPrecedence : Map<'Terminal, Associativity * PrecedenceLevel>;
    /// For production rules with a %prec declaration, maps the production rule
    /// to the terminal specified in the declaration.
    ProductionRulePrecedenceOverrides : Map<'Nonterminal * Symbol<'Nonterminal, 'Terminal>[], 'Terminal>;
    //
    StartSymbols : Set<'Nonterminal>;
}

//
type PrecompilationState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    (*  The precompilation state is a tuple of a ProcessedSpecification
        (the "result") and a ValidationMessages record (the "messages"). *)
    ProcessedSpecification<'Nonterminal, 'Terminal> * ValidationMessages

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private PrecompilationState =
    /// The empty precompilation state.
    let empty : PrecompilationState<'Nonterminal, 'Terminal> =
        // The 'result' component.
        {   Header = None;
            Nonterminals = Map.empty;
            Terminals = Map.empty;
            ProductionRules = Map.empty;
            TerminalPrecedence = Map.empty;
            ProductionRulePrecedenceOverrides = Map.empty;
            StartSymbols = Set.empty; },
        // The 'messages' component.
        {   Errors = List.empty;
            Warnings = List.empty; }

    //
    let inline result (precompilationState : PrecompilationState<'Nonterminal, 'Terminal>) =
        fst precompilationState, precompilationState

    //
    let inline messages (precompilationState : PrecompilationState<'Nonterminal, 'Terminal>) =
        snd precompilationState, precompilationState

    /// Adds an error message to the precompilation state.
    let addError message (precompilationState : PrecompilationState<'Nonterminal, 'Terminal>)
        : unit * PrecompilationState<_,_> =
        // Destructure the precompilation state to get it's components.
        let result, messages = precompilationState
        (), (result,
            { messages with
                Errors = message :: messages.Errors; })

    /// Adds a warning message to the precompilation state.
    let addWarning message (precompilationState : PrecompilationState<'Nonterminal, 'Terminal>)
        : unit * PrecompilationState<_,_> =
        // Destructure the precompilation state to get it's components.
        let result, messages = precompilationState
        (), (result,
            { messages with
                Warnings = message :: messages.Warnings; })

    //
    let setHeader header (precompilationState : PrecompilationState<'Nonterminal, 'Terminal>)
        : unit * PrecompilationState<_,_> =
        // Set the header contents.
        (), ({ fst precompilationState with
                Header = header; },
            snd precompilationState)

    //
    let addTerminal terminalId declaredType (precompilationState : PrecompilationState<'Nonterminal, 'Terminal>)
        : unit * PrecompilationState<_,_> =
        // Preconditions
        // TODO

        // Add the terminal and it's declared type to the table in the precompilation state.
        (), ({ (fst precompilationState) with
                Terminals = Map.add terminalId declaredType (fst precompilationState).Terminals; },
            snd precompilationState)

    //
    let addNonterminal nonterminalId declaredType (precompilationState : PrecompilationState<'Nonterminal, 'Terminal>)
        : unit * PrecompilationState<_,_> =
        // Preconditions
        // TODO
        
        // Add this nonterminal to the precompilation state.
        (), ({ (fst precompilationState) with
                Nonterminals = Map.add nonterminalId declaredType (fst precompilationState).Nonterminals; },
            snd precompilationState)

    //
    let addStartSymbol nonterminalId (precompilationState : PrecompilationState<'Nonterminal, 'Terminal>)
        : unit * PrecompilationState<_,_> =
        // Preconditions
        // TODO

        // Add this nonterminal to the set of start symbols.
        (), ({ (fst precompilationState) with
                    StartSymbols = Set.add nonterminalId (fst precompilationState).StartSymbols; },
                snd precompilationState)

    /// Sets the production rules for a nonterminal.
    let setProductionRules nonterminalId productionRules (precompilationState : PrecompilationState<'Nonterminal, 'Terminal>)
        : unit * PrecompilationState<_,_> =
        // Preconditions
        // TODO

        // Add the converted production rules into the precompilation state.
        (), ({ (fst precompilationState) with
                ProductionRules = Map.add nonterminalId productionRules (fst precompilationState).ProductionRules; },
            snd precompilationState)

    //
    let impersonateTerminal nonterminalId ruleSymbols impersonatedTerminal
        (precompilationState : PrecompilationState<'Nonterminal, 'Terminal>) : unit * PrecompilationState<_,_> =
        // Preconditions
        // TODO

        (), ({ (fst precompilationState) with
                    ProductionRulePrecedenceOverrides =
                        (fst precompilationState).ProductionRulePrecedenceOverrides
                        |> Map.add (nonterminalId, ruleSymbols) impersonatedTerminal; },
                snd precompilationState)

    /// Sets the precedence level and associativity of a terminal.
    let setTerminalPrecedence terminal associativity precedenceLevel
        (precompilationState : PrecompilationState<'Nonterminal, 'Terminal>) : unit * PrecompilationState<_,_> =
        (), ({ (fst precompilationState) with
                    TerminalPrecedence =
                        (fst precompilationState).TerminalPrecedence
                        |> Map.add terminal (associativity, precedenceLevel); },
                snd precompilationState)


/// Reserved terminal identifiers.
/// Defining a terminal with any of these identifiers will cause an error message
/// to be emitted when the parser specification is compiled.
let private reservedTerminalIdentifiers : Set<TerminalIdentifier> =
    Set.ofArray [|
        "error";
    |]

/// Validates the given parser specification, and compiles it into the
/// data structures used by the Graham library.
// TODO : The 'options' parameter may not actually be needed here, but we won't know until
// we really implement this function; however, it may be possible (and useful) to augment
// the "standard" validation checks with backend-specific checks, since some backends may not
// support all features.
let precompile (spec : Specification, options : CompilationOptions)
    : PrecompilationState<NonterminalIdentifier, TerminalIdentifier> =
    // Start with an empty precompilation state.
    PrecompilationState.empty
    |> state {
    // Copy some fields which don't need to be validated from the
    // original specification to the precompilation state.
    do! PrecompilationState.setHeader spec.Header

    (* NOTE :   In the code below, we fold *backwards* over the lists of declarations because they are all provided
                in reverse order (compared to the way they were ordered in the parser specification file). *)

    // Validation %token declarations of terminals.
    do! spec.TerminalDeclarations
        |> List.rev
        |> State.List.iter (fun (declaredType, terminalIds) ->
            terminalIds
            |> List.rev
            |> State.List.iter (fun terminalId ->
                state {
                // Has this nonterminal been declared already?
                let! result = PrecompilationState.result
                match Map.tryFind terminalId result.Terminals with
                | None ->
                    (* TODO : Also make sure this 'terminalId' hasn't been declared as a nonterminal. *)

                    // Is this a reserved terminal identifier?
                    if Set.contains terminalId reservedTerminalIdentifiers then
                        // Add an error message to the precompilation state.
                        let msg = sprintf "The identifier '%s' is reserved and may not be used for user-defined tokens." terminalId
                        do! PrecompilationState.addError msg
                    else
                        // Add the terminal and it's declared type to the table in the precompilation state.
                        do! PrecompilationState.addTerminal terminalId declaredType
                
                | Some existingDeclaredType ->
                    (*  This terminal has already been declared!
                        If the previous declaration has the same declared type, emit a warning message;
                        if it has a different declared type, emit an error message. *)
                    if existingDeclaredType = declaredType then
                        // Add the warning message into the precompilation state.
                        let msg = sprintf "Duplicate declaration of the terminal '%s'." terminalId
                        do! PrecompilationState.addWarning msg
                    else
                        let msg =
                            match existingDeclaredType with
                            | None ->
                                sprintf "The terminal '%s' has already been declared without a data type." terminalId
                            | Some existingDeclaredType ->
                                sprintf "The terminal '%s' has already been declared with the type '%s'." terminalId existingDeclaredType

                        // Add the error message into the precompilation state.
                        do! PrecompilationState.addError msg
                        }))

    // Validate the nonterminals "declared" via production rules.
    // NOTE : Only the nonterminals themselves are validated here --
    // the production rules themselves are validated later.
    do! spec.Productions
        |> List.rev
        |> State.List.iter (fun (nonterminalId, _) ->
            state {
            // Has this nonterminal been declared already?
            let! result = PrecompilationState.result
            if Map.containsKey nonterminalId result.Nonterminals then
                // Add an error message into the compilation state.
                // TODO : Add a better error message.
                let msg = "Production rules can only be declared once for each nonterminal."
                do! PrecompilationState.addError msg

            elif Map.containsKey nonterminalId result.Terminals then
                // Can't have production rules for a terminal
                // TODO : Add a better error message.
                let msg = "Production rules cannot be declared for terminals."
                do! PrecompilationState.addError msg

            else
                // Add this nonterminal to the precompilation state.
                do! PrecompilationState.addNonterminal nonterminalId None
            })

    // Validate %type declarations of nonterminals.
    do! spec.NonterminalDeclarations
        |> List.rev
        |> State.List.iter (fun (declaredType, nonterminalId) ->
            state {
            // Has this nonterminal been declared?
            let! result = PrecompilationState.result
            match Map.tryFind nonterminalId result.Nonterminals with
            | None ->
                // To provide a better error message, check if this is a terminal identifier.
                match Map.tryFind nonterminalId result.Terminals with
                | None ->
                    // Add an error message into the precompilation state.
                    let msg = sprintf "Undeclared nonterminal '%s'. Type declarations can only be made for nonterminals declared via production rules."
                                nonterminalId
                    do! PrecompilationState.addError msg

                | Some _ ->
                    // Add an error message into the precompilation state.
                    let msg = "Type declarations (%%type) cannot be applied to terminals. The %%token declaration should be used instead."
                    do! PrecompilationState.addError msg

            | Some None ->
                // Add the nonterminal and it's declared type to the table in the precompilation state.
                do! PrecompilationState.addNonterminal nonterminalId (Some declaredType)
            
            | Some (Some existingDeclaredType) ->
                (*  If the previous declaration has the same declared type, emit a warning message;
                    if it has a different declared type, emit an error message. *)
                if existingDeclaredType = declaredType then
                    // Add a warning message into the precompilation state.
                    let msg = sprintf "Duplicate %%type declaration for the nonterminal '%s'." nonterminalId
                    do! PrecompilationState.addWarning msg
                else
                    // Add an error message into the precompilation state.
                    let msg =
                        sprintf "The nonterminal '%s' has already been declared to have the type '%s'."
                            nonterminalId existingDeclaredType
                    do! PrecompilationState.addError msg
            })

    // The specification must declare at least one nonterminal as a starting production.
    // All nonterminals declared as starting productions must have type declarations.
    match spec.StartingProductions with
    | [] ->
        let msg = "The specification must declare at least one (1) nonterminal as a starting nonterminal via the %start declaration."
        do! PrecompilationState.addError msg
    | startingProductions ->
        do! startingProductions
            |> List.rev
            |> State.List.iter (fun nonterminalId ->
                state {
                // Has this nonterminal been declared?
                let! result = PrecompilationState.result
                match Map.tryFind nonterminalId result.Nonterminals with
                | None ->
                    // Add an error message into the precompilation state.
                    let msg = sprintf "The nonterminal '%s' is not defined." nonterminalId
                    do! PrecompilationState.addError msg

                | Some None ->
                    // Add an error message into the precompilation state.
                    let msg = sprintf "The type of nonterminal '%s' has not been declared. \
                                        Nonterminals used as starting productions must have their types declared with a %%type declaration."
                                        nonterminalId
                    do! PrecompilationState.addError msg

                | Some (Some _) ->
                    // Is this a duplicate %start declaration?
                    if Set.contains nonterminalId result.StartSymbols then
                        // Add a warning message to the precompilation state.
                        let msg = sprintf "Duplicate %%start declaration for the nonterminal '%s'." nonterminalId
                        do! PrecompilationState.addWarning msg
                    else
                        // Add this nonterminal to the set of start symbols in the precompilation state.
                        do! PrecompilationState.addStartSymbol nonterminalId
                        })

    // Validate the production rules.
    // Determine which, if any, of the terminals used in the precedence-override declarations are "dummy" terminals.
    let! dummyTerminals =
        (Set.empty, List.rev spec.Productions)
        ||> State.List.fold (fun dummyTerminals (nonterminalId, rules) ->
            state {
            // Make sure the symbols used in the production rules have all been declared.
            // OPTIMIZE : Both the validation and the conversion to Graham.Grammar.Symbol could be done in a single pass.
            let! productionRulesValid =
                (* Fold forward here, because the ordering doesn't matter. *)
                (true, rules)
                ||> State.List.fold (fun productionRulesValid rule ->
                    (productionRulesValid, rule.Symbols)
                    ||> State.List.fold (fun productionRulesValid symbolId ->
                        state {
                        // Is this symbol a defined terminal or nonterminal?
                        // Or a reserved (built-in) terminal?
                        let! result = PrecompilationState.result
                        if Map.containsKey symbolId result.Nonterminals
                            || Map.containsKey symbolId result.Terminals
                            (*|| Set.contains symbolId reservedTerminalIdentifiers*) then
                            return productionRulesValid
                        else
                            // Undefined symbol; add an error message to the precompilation state.
                            let msg = sprintf "Undeclared symbol '%s'." symbolId
                            do! PrecompilationState.addError msg
                            return false
                            }))

            // Convert the production rules into the form needed for use with Graham,
            // then add them into the precompilation state.
            if not productionRulesValid then
                // An error was found when validating the production rules, so don't bother processing them.
                return dummyTerminals
            else
                let! result = PrecompilationState.result
                /// The production rules for this nonterminal.
                let productionRules : ProcessedProductionRule<_,_>[] =
                    // OPTIMIZE : Use List.revMapIntoArray here to avoid unnecessary intermediate data structures.
                    rules
                    |> List.rev
                    |> List.toArray
                    |> Array.map (fun rule ->
                        { Symbols =
                            rule.Symbols
                            |> List.rev
                            |> List.toArray
                            |> Array.map (fun symbolId ->
                                if Map.containsKey symbolId result.Nonterminals then
                                    Symbol.Nonterminal symbolId
                                else
                                    Symbol.Terminal symbolId);
                          Action = rule.Action; })

                // Add the converted production rules into the precompilation state.
                do! PrecompilationState.setProductionRules nonterminalId productionRules

                // Validate the %prec declarations (if present) for these rules.
                // OPTIMIZE : Combine this with the rule conversion (above) to avoid re-converting the rules.
                return!
                    (dummyTerminals, rules)
                    ||> State.List.fold (fun dummyTerminals rule ->
                        state {
                        // Does this rule have a %prec declaration?
                        match rule.ImpersonatedPrecedence with
                        | None ->
                            return dummyTerminals
                        | Some impersonatedTerminal ->
                            let! result = PrecompilationState.result
                            let ruleSymbols =
                                rule.Symbols
                                |> List.rev
                                |> List.toArray
                                |> Array.map (fun symbolId ->
                                    if Map.containsKey symbolId result.Nonterminals then
                                        Symbol.Nonterminal symbolId
                                    else
                                        Symbol.Terminal symbolId)

                            // Make sure the impersonated identifier is not already declared as a nonterminal.
                            if Map.containsKey impersonatedTerminal result.Nonterminals then
                                // Nonterminals can't be impersonated -- add an error message to the precompilation state.
                                let msg = "Nonterminals cannot be impersonated by %prec declarations."
                                do! PrecompilationState.addError msg
                                return dummyTerminals
                            else
                                // Is this a declared terminal? If not, it'll become a dummy terminal.
                                let dummyTerminals =
                                    if Map.containsKey impersonatedTerminal result.Terminals then
                                        dummyTerminals
                                    else
                                        Set.add impersonatedTerminal dummyTerminals

                                do! PrecompilationState.impersonateTerminal nonterminalId ruleSymbols impersonatedTerminal
                                return dummyTerminals
                        })
            })

    // Validate the precedence/associativity declarations.
    let! dummyTerminalsWithoutPrecedence =
        (* NOTE :   We REQUIRE the associativity/precedence to be specified for any dummy terminals
                    defined by the %prec declaration of a production rule. *)
        ((dummyTerminals, (1<_> : PrecedenceLevel)), List.rev spec.Associativities)
        ||> State.List.fold (fun (dummyTerminalsWithoutPrecedence, precedenceLevel) (associativity, terminals) ->
            state {
            let! terminalSet =
                (Set.empty, List.rev terminals)
                ||> State.List.fold (fun terminalSet terminal ->
                    state {
                    // Has the associativity/precedence already been declared for this terminal?
                    let! result = PrecompilationState.result
                    if Map.containsKey terminal result.TerminalPrecedence then
                        // If the previous declaration was within this precedence "group",
                        // then just emit a warning about the duplicate declaration.
                        // Otherwise, emit an error because we don't know which precedence
                        // the terminal is really supposed to belong to.
                        if Set.contains terminal terminalSet then
                            let msg = sprintf "Duplicate associativity declaration for '%s'." terminal
                            do! PrecompilationState.addWarning msg
                            return terminalSet
                        else
                            let msg = sprintf "Duplicate associativity declaration for '%s' which conflicts with an earlier declaration." terminal
                            do! PrecompilationState.addError msg
                            return terminalSet
                    else
                        // Add this terminal to the set of terminals in this precedence "group".
                        let terminalSet = Set.add terminal terminalSet

                        // Add the associativity and precedence for this terminal to the precompilation state.
                        do! PrecompilationState.setTerminalPrecedence terminal associativity precedenceLevel
                        return terminalSet
                    })                

            // Remove any terminals in this set from the set of dummy terminals without precedences.
            let dummyTerminalsWithoutPrecedence =
                Set.difference dummyTerminalsWithoutPrecedence terminalSet
            
            return
                dummyTerminalsWithoutPrecedence,
                precedenceLevel + 1<_>
            })
        // Discard the precedence level counter
        |> State.map fst

    // Add error messages to the precompilation state for any dummy terminals which
    // don't have associativity declarations.
    do! dummyTerminalsWithoutPrecedence
        |> State.Set.iter (fun dummyTerminal ->
            state {
            let msg = sprintf "The terminal '%s' does not have an associativity declaration. \
                                'Dummy' terminals are required to have associativity declarations."
                                dummyTerminal
            do! PrecompilationState.addError msg
            })
    }
    // Return the final precompilation state.
    |> snd

/// Creates a PrecedenceSettings record from a ProcessedSpecification.
let private precedenceSettings (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>,
                                productionRuleIds : Map<AugmentedNonterminal<_> * AugmentedSymbol<_,_>[], ProductionRuleId>)
    : PrecedenceSettings<TerminalIdentifier> =
    //
    let rulePrecedence =
        (Map.empty, processedSpec.ProductionRules)
        ||> Map.fold (fun rulePrecedence nonterminal rules ->
            (rulePrecedence, rules)
            ||> Array.fold (fun rulePrecedence rule ->
                /// The identifier for this production rule.
                let productionRuleId =
                    //
                    let augmentedKey =
                        AugmentedNonterminal.Nonterminal nonterminal,
                        rule.Symbols
                        |> Array.map (function
                            | Nonterminal nonterminal ->
                                Nonterminal <| AugmentedNonterminal.Nonterminal nonterminal
                            | Terminal terminal ->
                                Terminal <| AugmentedTerminal.Terminal terminal)

                    Map.find augmentedKey productionRuleIds

                /// The terminal whose associativity and precedence is impersonated by this production rule.
                let precedenceTerminal =
                    // Does this rule have a precedence override declaration?
                    match Map.tryFind (nonterminal, rule.Symbols) processedSpec.ProductionRulePrecedenceOverrides with
                    | Some impersonatedTerminal ->
                        Some impersonatedTerminal
                    | None ->
                        // The precedence of a rule is the precedence of it's last (right-most) terminal.
                        match System.Array.FindLastIndex (rule.Symbols, System.Predicate (function Terminal _ -> true | Nonterminal _ -> false)) with
                        //match System.Array.FindIndex (rule.Symbols, (function Terminal _ -> true | Nonterminal _ -> false)) with
                        | -1 ->
                            // This rule does not contain any terminals, so it is not assigned a precedence.
                            None
                        | lastTerminalIndex ->
                            match rule.Symbols.[lastTerminalIndex] with
                            | Terminal terminal ->
                                Some terminal
                            | Nonterminal _ ->
                                failwith "Found a nonterminal where a terminal was expected."

                // If this rule can be assigned a precedence, add it to the rule precedence map now.
                match precedenceTerminal with
                | None ->
                    rulePrecedence
                | Some precedenceTerminal ->
                    // The associativity and precedence of the impersonated terminal.
                    match Map.tryFind precedenceTerminal processedSpec.TerminalPrecedence with
                    | None ->
                        // The terminal has no precedence, so the rule has no precedence.
                        rulePrecedence
                    | Some impersonatedTerminalPrecedence ->
                        // Add the precedence to the rule precedence map.
                        Map.add productionRuleId impersonatedTerminalPrecedence rulePrecedence
                    ))

    // Filter any "dummy" terminals out of the terminal precedence map.
    let terminalPrecedence =
        processedSpec.TerminalPrecedence
        |> Map.filter (fun terminal _ ->
            Map.containsKey terminal processedSpec.Terminals)

    // Create and return a PrecedenceSettings record from the constructed precedence maps.
    {   TerminalPrecedence = terminalPrecedence;
        RulePrecedence = rulePrecedence; }    

/// Compiles a parser specification into a deterministic pushdown automaton (DPDA),
/// then invokes a specified backend to generate code implementing the parser automaton.
let compile (processedSpec : ProcessedSpecification<_,_>, options : CompilationOptions) : Choice<_,_> =
    /// The grammar created from the parser specification.
    let grammar =
        //
        let rawGrammar : Grammar<_,_> = {
            Terminals =
                (Set.empty, processedSpec.Terminals)
                ||> Map.fold (fun terminals terminal _ ->
                    Set.add terminal terminals);
            Nonterminals =
                (Set.empty, processedSpec.Nonterminals)
                ||> Map.fold (fun nonterminals nonterminal _ ->
                    Set.add nonterminal nonterminals);
            Productions =
                processedSpec.ProductionRules
                |> Map.map (fun _ rules ->
                    rules |> Array.map (fun rule -> rule.Symbols)); }

        // Augment the grammar.
        Grammar.Augment (rawGrammar, processedSpec.StartSymbols)

    /// The production-rule-id lookup table.
    let productionRuleIds =
        Grammar.ProductionRuleIds grammar

    // Create the precedence settings (precedence and associativity maps)
    // from the precompilation result.
    let precedenceSettings =
        precedenceSettings (processedSpec, productionRuleIds)

    (*  Create the LR(0) automaton from the grammar; report the number of states and
        the number of S/R and R/R conflicts. If there are any conflicts, apply the
        precedence table to the constructed parser table to (possibly) resolve some
        of them. At this point, if there aren't any remaining conflicts, report that
        the grammar is LR(0) and return. *)
    //
    let lr0Table = Lr0.createTable grammar

    (*  Upgrade the LR(0) automaton to SLR(1); report the remaining number of S/R and
        R/R conflicts. If there aren't any remaining conflicts, report that the grammar
        is SLR(1) and return. *)
    //
    let slr1Table = Slr1.upgrade (grammar, lr0Table, productionRuleIds)        

    (*  Upgrade the LR(0)/SLR(1) automaton to LALR(1); report the remaining number of
        S/R and R/R conflicts. If there aren't any remaining conflicts, report that the
        grammar is LALR(1) and return. *)
    //
    let lalrLookaheadSets =
        Lalr1.lookaheadSets (grammar, slr1Table)

    // If we detected that the grammar is not LR(k), stop and return an error message.
    match lalrLookaheadSets with
    | Choice2Of2 errorMessage ->
        Choice2Of2 [errorMessage]
    | Choice1Of2 lookaheadSets ->
        //
        let lalr1Table =
            Lalr1.upgrade (grammar, slr1Table, productionRuleIds, lookaheadSets)

        (* Apply precedence settings to resolve as many conflicts as possible. *)
        /// The LALR(1) parser table, after applying precedence settings.
        let lalr1Table =
            // Apply precedences to resolve conflicts.
            Lr0.applyPrecedence (lalr1Table, precedenceSettings)
            
        (*  If we reach this point, the grammar is not LALR(1), but we can still create a
            parser by taking certain actions to resolve any remaining conflicts.
            Emit a _warning_ message for each of these conflicts, specifying the action
            we've taken to resolve it. *)
        //
        let lalr1Table =
            Lr0.resolveConflicts lalr1Table

        // Return the compiled parser table.
        Choice1Of2 lalr1Table

