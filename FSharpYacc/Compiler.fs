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

open NLog
open ExtCore.Printf
open ExtCore.Control
open ExtCore.Control.Collections
open Graham
open Graham.LR
open FSharpYacc.Ast


(* TODO :   Move the implementation of the rule-precedence-map creation into Graham. *)

//
[<RequireQualifiedAccess>]
module internal PrecedenceSettings =
(*
    //
    [<System.Obsolete("This function is deprecated. A replacement which uses TaggedGrammar should be implemented and used instead.")>]
    let private productionRuleIds (grammar : Grammar<'Nonterminal, 'Terminal>) =
        (Map.empty, grammar)
        ||> Map.fold (fun productionRuleIds nonterminal rules ->
            (productionRuleIds, rules)
            ||> Array.fold (fun productionRuleIds ruleRhs ->
                /// The identifier for this production rule.
                let productionRuleId : ProductionRuleIndex =
                    tag <| Map.count productionRuleIds

                // Add this identifier to the map.
                Map.add (nonterminal, ruleRhs) productionRuleId productionRuleIds))
*)

    /// Creates a rule-precedence map from a tagged, augmented grammar.
    let private rulePrecedence (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (terminalPrecedence : TagMap<TerminalIndexTag, Associativity * AbsolutePrecedenceLevel>)
        (productionRulePrecedenceOverrides : TagMap<ProductionRuleIndexTag, TerminalIndex>)
        : TagMap<ProductionRuleIndexTag, Associativity * AbsolutePrecedenceLevel> =
        (TagMap.empty, taggedGrammar.Productions)
        ||> TagMap.fold (fun rulePrecedence ruleIndex rule ->
            /// The terminal whose associativity and precedence is impersonated by this production rule.
            let precedenceTerminal =
                // Does this rule have a precedence override declaration?
                match TagMap.tryFind ruleIndex productionRulePrecedenceOverrides with
                | Some impersonatedTerminalIndex ->
                    Some impersonatedTerminalIndex
                | None ->
                    // The precedence of a rule is the precedence of it's last (right-most) terminal.
                    // OPTIMIZE : Use Array.chooseBack from ExtCore.
                    match System.Array.FindLastIndex (rule, System.Predicate (function Symbol.Terminal _ -> true | Symbol.Nonterminal _ -> false)) with
                    //match System.Array.FindIndex (rule, (function Symbol.Terminal _ -> true | Symbol.Nonterminal _ -> false)) with
                    | -1 ->
                        // This rule does not contain any terminals, so it is not assigned a precedence.
                        None
                    | indexOfLastTerminal ->
                        match rule.[indexOfLastTerminal] with
                        | Symbol.Terminal terminalIndex ->
                            Some terminalIndex
                        | Symbol.Nonterminal _ ->
                            failwith "Found a nonterminal where a terminal was expected."

            // If this rule can be assigned a precedence, add it to the rule precedence map now.
            match precedenceTerminal with
            | None ->
                rulePrecedence
            | Some precedenceTerminal ->
                // The associativity and precedence of the impersonated terminal.
                match TagMap.tryFind precedenceTerminal terminalPrecedence with
                | None ->
                    // The terminal has no precedence, so the rule has no precedence.
                    rulePrecedence
                | Some impersonatedTerminalPrecedence ->
                    // Add the precedence to the rule precedence map.
                    TagMap.add ruleIndex impersonatedTerminalPrecedence rulePrecedence
                )

    //
    let private terminalPrecedence (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
        : TagMap<TerminalIndexTag, Associativity * AbsolutePrecedenceLevel> =
        // TODO
        notImpl "PrecedenceSettings.terminalPrecedence"

    //
    let private productionRulePrecedenceOverrides (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
        : TagMap<ProductionRuleIndexTag, TerminalIndex> =
        // TODO
        notImpl "PrecedenceSettings.productionRulePrecedenceOverrides"

    /// Creates a PrecedenceSettings record from a ProcessedSpecification.
    let internal create (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>) : PrecedenceSettings =
        /// The terminal precedence map from the ProcessedSpecification,
        /// converted to use the tagged-indices from the tagged-grammar.
        let terminalPrecedence = terminalPrecedence taggedGrammar processedSpec

        //
        let rulePrecedence =
            productionRulePrecedenceOverrides taggedGrammar processedSpec
            |> rulePrecedence taggedGrammar terminalPrecedence

        // Filter any "dummy" terminals out of the terminal precedence map.
        // NOTE : This must be done _AFTER_ the rule-precedence map is created,
        // because it relies on the dummy terminals to work correctly.
        let terminalPrecedence =
            let terminalPrecedence =
                processedSpec.TerminalPrecedence
                |> Map.filter (fun terminal _ ->
                    Map.containsKey terminal processedSpec.Terminals)

            (TagMap.empty, terminalPrecedence)
            ||> Map.fold (fun terminalPrecedence terminal value ->
                let terminalIndex = TagBimap.findValue (AugmentedTerminal.Terminal terminal) taggedGrammar.Terminals
                TagMap.add terminalIndex value terminalPrecedence)

        // Create and return a PrecedenceSettings record from the constructed precedence maps.
        {   TerminalPrecedence = terminalPrecedence;
            RulePrecedence = rulePrecedence; }


/// Invokes a function. An information message is written to a Logger before the
/// function is invoked then again when it returns.
let private logInfo (logger : Logger) message (generator : unit -> 'T) : 'T =
    logger.Info ("Start: " + message)
    let result = generator ()
    logger.Info ("End: " + message)
    result

/// <summary>
/// Compiles a parser specification into a deterministic pushdown automaton (DPDA),
/// then invokes a specified backend to generate code implementing the parser automaton.
/// </summary>
/// <param name="processedSpec">The processed parser specification.</param>
/// <param name="taggedGrammar">The tagged grammar created from the processed parser specification.</param>
/// <param name="options">Compiler options.</param>
/// <param name="logger">Records information about the compilation process.</param>
let compile (processedSpec : ProcessedSpecification<_,_>) (taggedGrammar : AugmentedTaggedGrammar<_,_,_>)
    (options : CompilationOptions) (logger : Logger) : Choice<_,_> =
    choice {
    logger.Info "Start: Compilation of parser specification."

    /// The predictive sets (FIRST, FOLLOW, NULLABLE) for the grammar.
    let predictiveSets =
        logInfo logger "Compute the predictive sets of the grammar." <| fun () ->
            Analysis.PredictiveSets.ofGrammar taggedGrammar

    (*  Create the LR(0) automaton from the grammar; report the number of states and
        the number of S/R and R/R conflicts. If there are any conflicts, apply the
        precedence table to the constructed parser table to (possibly) resolve some
        of them. At this point, if there aren't any remaining conflicts, report that
        the grammar is LR(0) and return. *)
    
    /// The LR(0) parser table.
    let lr0Table =
        logInfo logger "Create the LR(0) parser table." <| fun () ->
            Lr0.createTable taggedGrammar

    (*  Upgrade the LR(0) automaton to SLR(1); report the remaining number of S/R and
        R/R conflicts. If there aren't any remaining conflicts, report that the grammar
        is SLR(1) and return. *)
    //
    let slr1Table =
        logInfo logger "Upgrade the LR(0) parser table to SLR(1)." <| fun () ->
            Slr1.upgrade taggedGrammar lr0Table (Some predictiveSets)

    (*  Upgrade the LR(0)/SLR(1) automaton to LALR(1); report the remaining number of
        S/R and R/R conflicts. If there aren't any remaining conflicts, report that the
        grammar is LALR(1) and return. *)
    //
    let! lalrLookaheadSets =
        logInfo logger "Compute LALR(1) look-ahead sets." <| fun () ->
            Lalr1.lookaheadSets taggedGrammar slr1Table

    //
    let lalr1Table =
        logInfo logger "Upgrade the SLR(1) parser table to LALR(1)." <| fun () ->
            Lalr1.upgrade taggedGrammar slr1Table lalrLookaheadSets (Some predictiveSets)

    (* Apply precedence settings to resolve as many conflicts as possible. *)

    // Create the precedence settings (precedence and associativity maps) from the processed specification.
    let precedenceSettings =
        logInfo logger "Compile precedence settings." <| fun () ->
            PrecedenceSettings.create taggedGrammar processedSpec

    /// The LALR(1) parser table, after applying precedence settings.
    let lalr1Table =
        logInfo logger "Apply precedence declarations." <| fun () ->
            // Apply precedences to resolve conflicts.
            ConflictResolution.applyPrecedence lalr1Table precedenceSettings
            
    (*  If we reach this point, the grammar is not LALR(1), but we can still create a
        parser by taking certain actions to resolve any remaining conflicts.
        Emit a _warning_ message for each of these conflicts, specifying the action
        we've taken to resolve it. *)
    //
    let lalr1Table =
        logInfo logger "Use default strategy to solve remaining conflicts." <| fun () ->
            ConflictResolution.resolveConflicts lalr1Table

    // Return the compiled parser table.
    logger.Info "End: Compilation of parser specification."
    return lalr1Table
    }

/// <summary>Compiles a parser specification into an augmented, tagged grammar.</summary>
/// <param name="processedSpec">The processed parser specification.</param>
let specToGrammar (processedSpec : ProcessedSpecification<_,_>)
    : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType> =
    /// The grammar created from the parser specification.
    let rawGrammar : Grammar<_,_> =
        processedSpec.ProductionRules
        |> Map.map (fun _ rules ->
            rules |> Array.map (fun rule -> rule.Symbols))

    /// The tagged grammar created from the parser specification.
    let taggedGrammar = TaggedGrammar.ofGrammar rawGrammar

    // For completeness, make sure all terminals and nonterminals declared in the specification
    // are included in the tagged grammar. This ensures that declared terminals and nonterminals
    // which aren't used in any production rules are still included in the tagged grammar, which
    // is important for certain backends (and for various grammar analyses).
    let taggedGrammar =
        (taggedGrammar, processedSpec.Terminals)
        ||> Map.fold (fun taggedGrammar terminal _ ->
            if TagBimap.containsValue terminal taggedGrammar.Terminals then
                taggedGrammar
            else
                let terminalIndex = tag <| TagBimap.count taggedGrammar.Terminals
                { taggedGrammar with
                    Terminals = TagBimap.add terminalIndex terminal taggedGrammar.Terminals; })

    let taggedGrammar =
        (taggedGrammar, processedSpec.Nonterminals)
        ||> Map.fold (fun taggedGrammar nonterminal _ ->
            if TagBimap.containsValue nonterminal taggedGrammar.Nonterminals then
                taggedGrammar
            else
                let nonterminalIndex = tag <| TagBimap.count taggedGrammar.Nonterminals
                { taggedGrammar with
                    Nonterminals = TagBimap.add nonterminalIndex nonterminal taggedGrammar.Nonterminals; })

    // Augment the tagged grammar with the Start nonterminal, EndOfFile terminal,
    // and new production rules for the Start nonterminal.
    AugmentedTaggedGrammar.augmentWith taggedGrammar processedSpec.StartSymbols
