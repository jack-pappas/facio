﻿(*

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
namespace Graham.Analysis

open ExtCore
open ExtCore.Collections
open Graham.Grammar


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
    let computeNullable (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) =
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
                            |> Array.exists (Array.forall (function
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
    let inline internal allNullableInSlice (production : Symbol<'Nonterminal, 'Terminal>[], startInclusive, endInclusive, nullable : Map<'Nonterminal, bool>) =
        (startInclusive, endInclusive)
        ||> Range.forall (fun index ->
            match production.[index] with
            | Symbol.Terminal _ ->
                false
            | Symbol.Nonterminal nontermId ->
                Map.find nontermId nullable)

    //
    let computeFirst (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>, nullable : Map<'Nonterminal, bool>) =
        /// Implementation of the algorithm for computing the FIRST sets of the nonterminals.
        let rec computeFirst (firstSets : Map<'Nonterminal, Set<'Terminal>>) =
            let firstSets, updated =
                ((firstSets, false), productions)
                ||> Map.fold (fun (firstSets, updated) nontermId productions ->
                    ((firstSets, updated), productions)
                    ||> Array.fold (fun (firstSets, updated) production ->
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
    let computeFollow (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>,
                                nullable : Map<AugmentedNonterminal<'Nonterminal>, bool>,
                                firstSets : Map<AugmentedNonterminal<'Nonterminal>, Set<AugmentedTerminal<'Terminal>>>) =
        /// Implementation of the algorithm for computing the FOLLOW sets of the nonterminals.
        let rec computeFollow (followSets : Map<AugmentedNonterminal<'Nonterminal>, Set<AugmentedTerminal<'Terminal>>>) =
            let followSets, updated =
                ((followSets, false), grammar.Productions)
                ||> Map.fold (fun (followSets, updated) nontermId productions ->
                    ((followSets, updated), productions)
                    ||> Array.fold (fun (followSets, updated) production ->
                        let mutable followSets = followSets
                        let mutable updated = updated

                        let productionLength = Array.length production
                        for i = 0 to productionLength - 1 do
                            // Only compute follow sets for non-terminals!
                            match production.[i] with
                            | Symbol.Terminal _ -> ()
                            | Symbol.Nonterminal ithSymbolNontermId ->                            
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
    let ofGrammar (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) =
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


///// Reachability analyses on context-free grammars.
//[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
//module Reachability =
//    (* TODO :   These analyses are probably easiest to implement using a graph representation
//                of a grammar, so we'll also need to implement a decent sparse graph library. *)
//
//    // Detect unreachable/dead nonterminals
//    let unreachableNonterminals () =
//        notImpl "Grammar.unreachableNonterminals"
//
//    // Detect unreachable productions; i.e., productions overlapped
//    // by some earlier production of the same nonterminal.
//    let unreachableProductions () =
//        notImpl "Grammar.unreachableProductions"


(* TODO :   Implement an ambiguity detection module. *)

