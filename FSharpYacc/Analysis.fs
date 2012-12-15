(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.Analysis

open Grammar


//
type PredictiveSets<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    //
    First : Map<'Nonterminal, Set<'Terminal>>;
    //
    Follow : Map<'Nonterminal, Set<'Terminal>>;
    //
    Nullable : Map<'Nonterminal, bool>;
}

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module PredictiveSets =
    (* OPTIMIZE :   The functions in this module can be sped up by creating a dependency graph of
                    the nonterminals in the grammar, then computing a quasi-topological sort of
                    this graph. Traversing this graph from the bottom up will minimize the number
                    of iterations needed to reach a fixpoint. *)
    (* OPTIMIZE :   Modify the functions in this module to use a worklist-style algorithm to
                    avoid re-processing values which haven't changed. *)

    //
    let internal computeNullable (productions : Map<'Nonterminal, Set<Symbol<'Nonterminal, 'Terminal>[]>>) =
        /// Implementation of the nullable-map-computing algorithm.
        let rec computeNullable (nullable : Map<'Nonterminal, bool>) =
            let nullable, updated =
                ((nullable, false), productions)
                ||> Map.fold (fun (nullable, updated) nontermId productions ->
                    // If this nonterminal is already known to be nullable, skip it.
                    if Map.find nontermId nullable then
                        nullable, updated
                    else
                        /// When set, denotes that this nonterminal is nullable.
                        let isNullable =
                            productions
                            |> Set.exists (Array.forall (function
                                | Symbol.Terminal _ ->
                                    false
                                | Symbol.Nonterminal nontermId ->
                                    Map.find nontermId nullable))

                        // If this nonterminal is nullable, update its entry in the map.
                        if isNullable then
                            Map.add nontermId true nullable,
                            true    // Denotes the map has been updated
                        else
                            nullable, updated)

            // If the 'nullable' map has not been updated, we've reached
            // the fixpoint so return the computed map; otherwise, recurse
            // to continue computing.
            if updated then
                computeNullable nullable
            else
                nullable

        //
        productions
        |> Map.map (fun _ _ -> false)
        //
        |> computeNullable

    /// Determines if all symbols within the specified slice of a production are nullable.
    let inline private allNullableInSlice (production : Symbol<'Nonterminal, 'Terminal>[], startInclusive, endInclusive, nullable : Map<'Nonterminal, bool>) =
        let mutable result = true
        let mutable index = startInclusive
        while result && index <= endInclusive do
            result <-
                match production.[index] with
                | Symbol.Terminal _ ->
                    false
                | Symbol.Nonterminal nontermId ->
                    Map.find nontermId nullable

            // Increment the index
            index <- index + 1

        // Return the result
        result

    //
    let internal computeFirst (productions : Map<'Nonterminal, Set<Symbol<'Nonterminal, 'Terminal>[]>>, nullable : Map<'Nonterminal, bool>) =
        /// Implementation of the algorithm for computing the FIRST sets of the nonterminals.
        let rec computeFirst (firstSets : Map<'Nonterminal, Set<'Terminal>>) =
            let firstSets, updated =
                ((firstSets, false), productions)
                ||> Map.fold (fun (firstSets, updated) nontermId productions ->
                    ((firstSets, updated), productions)
                    ||> Set.fold (fun (firstSets, updated) production ->
                        let mutable firstSets = firstSets
                        let mutable updated = updated

                        for i = 0 to Array.length production - 1 do
                            if i = 0 || allNullableInSlice (production, 0, i - 1, nullable) then
                                /// The FIRST set for the current nonterminal.
                                let nontermFirstSet = Map.find nontermId firstSets
                                
                                /// The updated FIRST set for the current nonterminal.
                                let nontermFirstSet' =
                                    /// The FIRST set for the i-th symbol in the production.
                                    let symbolFirstSet =
                                        match production.[i] with
                                        | Symbol.Terminal token ->
                                            Set.singleton token
                                        | Symbol.Nonterminal nontermId ->
                                            Map.find nontermId firstSets
                                    
                                    Set.union nontermFirstSet symbolFirstSet

                                // Set the 'updated' flag iff the nonterminal's FIRST set
                                // was actually changed.
                                if nontermFirstSet <> nontermFirstSet' then
                                    updated <- true
                                    firstSets <- Map.add nontermId nontermFirstSet' firstSets

                        // Pass the 'firstSets' map and the 'updated' flag to the
                        // next iteration of the fold.
                        firstSets, updated))

            // If the 'firstSets' map has not been updated, we've reached
            // the fixpoint so return the computed map; otherwise, recurse
            // to continue computing.
            if updated then
                computeFirst firstSets
            else
                firstSets

        //
        productions
        |> Map.map (fun _ _ -> Set.empty)
        //
        |> computeFirst

    //
    let internal computeFollow (grammar : Grammar<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>>,
                                nullable : Map<AugmentedNonterminal<'Nonterminal>, bool>,
                                firstSets : Map<AugmentedNonterminal<'Nonterminal>, Set<AugmentedTerminal<'Terminal>>>) =
        /// Implementation of the algorithm for computing the FOLLOW sets of the nonterminals.
        let rec computeFollow (followSets : Map<AugmentedNonterminal<'Nonterminal>, Set<AugmentedTerminal<'Terminal>>>) =
            let followSets, updated =
                ((followSets, false), grammar.Productions)
                ||> Map.fold (fun (followSets, updated) nontermId productions ->
                    ((followSets, updated), productions)
                    ||> Set.fold (fun (followSets, updated) production ->
                        let mutable followSets = followSets
                        let mutable updated = updated

                        let productionLength = Array.length production
                        for i = 0 to productionLength - 1 do
                            // Only compute follow sets for non-terminals!
                            match production.[i] with
                            | Symbol.Terminal _ -> ()
                            | Symbol.Nonterminal ithSymbolNontermId ->
                                (* OPTIMIZE :   Both conditions here could be fused and simplified if we implemented a
                                                function similar to Array.tryPick, but which worked over a segment or slice
                                                of the array. (This function should be inlined.)
                                                The 'picker' function passed to this new function would return Some for any
                                                non-nullable symbol; then, if all the symbols were nullable (or the i-th symbol
                                                is the last symbol in the production), we'd "fill" the value with the
                                                FOLLOW set of the nonterminal producing this production. *)
                            
                                // If this nonterminal is the last symbol in the production, or all of the symbols
                                // which follow it are nullable (i.e., they could all be empty), then the FOLLOW set
                                // of this nonterminal must contain the FOLLOW set of the nonterminal producing this production.
                                if i = productionLength - 1 ||
                                    allNullableInSlice (production, i + 1, productionLength - 1, nullable) then
                                    /// The FOLLOW set for the i-th symbol in the production.
                                    let ithSymbolFollowSet = Map.find ithSymbolNontermId followSets

                                    /// The updated FOLLOW set for the i-th symbol in the production.
                                    let ithSymbolFollowSet' =
                                        /// The FOLLOW set for the current nonterminal.
                                        let nontermFollowSet = Map.find nontermId followSets
                                        // Merge it with the FOLLOW set for the i-th symbol.
                                        Set.union ithSymbolFollowSet nontermFollowSet

                                    // Set the 'updated' flag iff the i-th symbol's FOLLOW set
                                    // was actually changed.
                                    if ithSymbolFollowSet <> ithSymbolFollowSet' then
                                        updated <- true
                                        followSets <- Map.add ithSymbolNontermId ithSymbolFollowSet' followSets

                                // If there are any non-nullable symbols in the production which follow the i-th symbol,
                                // then merge the FIRST set of the first of those non-nullable symbols into the FOLLOW set
                                // of the i-th symbol; also merge the FIRST sets of any nullable symbols which appear
                                // prior to the first non-nullable symbol.
                                for j = i + 1 to productionLength - 1 do
                                    if i + 1 = j || allNullableInSlice (production, i + 1, j - 1, nullable) then
                                        /// The FOLLOW set for the i-th symbol in the production.
                                        let ithSymbolFollowSet = Map.find ithSymbolNontermId followSets

                                        /// The updated FOLLOW set for the i-th symbol in the production.
                                        let ithSymbolFollowSet' =
                                            /// The FIRST set for the j-th symbol in the production.
                                            let jthSymbolFirstSet =
                                                match production.[j] with
                                                | Symbol.Terminal token ->
                                                    Set.singleton token
                                                | Symbol.Nonterminal nontermId ->
                                                    Map.find nontermId firstSets

                                            Set.union ithSymbolFollowSet jthSymbolFirstSet

                                        // Set the 'updated' flag iff the i-th symbol's FOLLOW set
                                        // was actually changed.
                                        if ithSymbolFollowSet <> ithSymbolFollowSet' then
                                            updated <- true
                                            followSets <- Map.add ithSymbolNontermId ithSymbolFollowSet' followSets

                        // Pass the 'followSets' map and the 'updated' flag to the
                        // next iteration of the fold.
                        followSets, updated))

            // If the 'followSets' map has not been updated, we've reached
            // the fixpoint so return the computed map; otherwise, recurse
            // to continue computing.
            if updated then
                computeFollow followSets
            else
                followSets

        //
        grammar.Productions
        |> Map.map (fun nonterminal _ ->
            match nonterminal with
            | AugmentedNonterminal.Start ->
                // The FOLLOW set for the augmented start symbol
                // is initialized with the end-of-file marker.
                Set.singleton EndOfFile
            | AugmentedNonterminal.Nonterminal _ ->
                Set.empty)
        //
        |> computeFollow

    //
    let ofGrammar (grammar : Grammar<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>>) =
        /// Map denoting which nonterminals in the grammar are nullable.
        let nullable = computeNullable grammar.Productions

        /// The FIRST sets for the nonterminals in the grammar.
        let firstSets = computeFirst (grammar.Productions, nullable)

        /// The FOLLOW sets for the nonterminals in the grammar.
        let followSets = computeFollow (grammar, nullable, firstSets)

        // Combine the computed sets into a GrammarAnalysis record and return it.
        { Nullable = nullable;
            First = firstSets;
            Follow = followSets; }


/// Classifies a parser position (within a parser item), based on
/// how the insertion of a semantic routine at that position would
/// change the classification of the grammar.
type PositionClassification =
    /// No semantic routine may be called at this position.
    // Inserting a semantic routine here always causes the grammar
    // to become non-deterministic.
    | Forbidden
    /// It is sometimes safe to call a semantic routine at this position.
    // Inserting a semantic routine here may cause the grammar to
    // become non-deterministic.
    | Contingent
    /// It is always safe to call a semantic routine at this position.
    // Inserting a semantic routine here preserves the grammar class;
    // e.g., an LR(1) grammar will still be LR(1) after inserting the routine.
    | Free

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Grammar =
    (* TODO :   Implement functions to perform other useful analyses on grammars; for example:
                    - Detect unreachable/dead nonterminals
                    - Detect unreachable productions (i.e., productions overlapped by some earlier
                      production of the same nonterminal).
                    - Ambiguity detection.

                These analyses are probably easiest to implement using a graph representation
                of a grammar, so we'll also need to implement a decent sparse graph library. *)

    //
    let classifyPositions (grammar : Grammar<'Nonterminal, 'Terminal>) =
        // TODO : Need to implement some graph functionality (for dominators)
        // before this algorithm can be implemented.
        failwith "TODO"

