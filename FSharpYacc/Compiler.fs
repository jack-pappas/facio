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


/// Compiles a parser specification into a deterministic pushdown automaton (DPDA),
/// then invokes a specified backend to generate code implementing the parser automaton.
let compile (processedSpec : ProcessedSpecification<_,_>) (options : CompilationOptions) (logger : Logger) : Choice<_,_> =
    tprintfn "Compiling the parser specification..."

    /// The tagged grammar.
    let taggedGrammar =
        /// The grammar created from the parser specification and augmented with
        /// a starting production and the end-of-file marker.
        let grammar =
            /// The grammar created from the parser specification.
            let rawGrammar : Grammar<_,_> =
                processedSpec.ProductionRules
                |> Map.map (fun _ rules ->
                    rules |> Array.map (fun rule -> rule.Symbols))

            // Augment the grammar.
            Grammar.augmentWith rawGrammar processedSpec.StartSymbols
        
        TaggedGrammar.ofGrammar grammar

    // Create the precedence settings (precedence and associativity maps)
    // from the precompilation result.
    let precedenceSettings =
        tprintf "  Creating precedence settings..."
        let precedenceSettings = Prepare.precedenceSettings taggedGrammar processedSpec
        tprintfn "done."
        precedenceSettings

    (*  Create the LR(0) automaton from the grammar; report the number of states and
        the number of S/R and R/R conflicts. If there are any conflicts, apply the
        precedence table to the constructed parser table to (possibly) resolve some
        of them. At this point, if there aren't any remaining conflicts, report that
        the grammar is LR(0) and return. *)
    
    /// The LR(0) parser table.
    let lr0Table =
        tprintf "  Creating the LR(0) parser table..."
        let lr0Table = Lr0.createTable taggedGrammar
        tprintfn "done."
        lr0Table

    (*  Upgrade the LR(0) automaton to SLR(1); report the remaining number of S/R and
        R/R conflicts. If there aren't any remaining conflicts, report that the grammar
        is SLR(1) and return. *)
    //
    let slr1Table =
        tprintf "  Upgrading the LR(0) parser table to SLR(1)..."
        let slr1Table = Slr1.upgrade taggedGrammar lr0Table
        tprintfn "done."
        slr1Table

    (*  Upgrade the LR(0)/SLR(1) automaton to LALR(1); report the remaining number of
        S/R and R/R conflicts. If there aren't any remaining conflicts, report that the
        grammar is LALR(1) and return. *)
    //
    let lalrLookaheadSets =
        tprintf "  Computing LALR(1) look-ahead sets..."
        let lalrLookaheadSets = Lalr1.lookaheadSets taggedGrammar slr1Table
        tprintfn "done."
        lalrLookaheadSets

    // If we detected that the grammar is not LR(k), stop and return an error message.
    match lalrLookaheadSets with
    | Choice2Of2 errorMessage ->
        Choice2Of2 [errorMessage]
    | Choice1Of2 lookaheadSets ->
        //
        let lalr1Table =
            tprintf "  Upgrading the SLR(1) parser table to LALR(1)..."
            let lalr1Table = Lalr1.upgrade taggedGrammar slr1Table lookaheadSets None
            tprintfn "done."
            lalr1Table

        (* Apply precedence settings to resolve as many conflicts as possible. *)
        /// The LALR(1) parser table, after applying precedence settings.
        let lalr1Table =
            tprintf "  Applying precedence declarations..."
            // Apply precedences to resolve conflicts.
            let lalr1Table = ConflictResolution.applyPrecedence lalr1Table precedenceSettings
            tprintfn "done."
            lalr1Table
            
        (*  If we reach this point, the grammar is not LALR(1), but we can still create a
            parser by taking certain actions to resolve any remaining conflicts.
            Emit a _warning_ message for each of these conflicts, specifying the action
            we've taken to resolve it. *)
        //
        let lalr1Table =
            tprintf "  Using default strategy to solve any remaining conflicts..."
            let lalr1Table = ConflictResolution.resolveConflicts lalr1Table
            tprintfn "done."
            lalr1Table

        // Return the compiled parser table.
        tprintfn "Finished compiling the parser specification."
        Choice1Of2 lalr1Table

