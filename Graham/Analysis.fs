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
namespace Graham.Analysis

open Graham


//
type PredictiveSets = {
    //
    // OPTIMIZE : Change this to use a TagMultimap once it's available in ExtCore.
    First : TagMap<NonterminalIndexTag, TagSet<TerminalIndexTag>>;
    //
    // OPTIMIZE : Change this to use a TagMultimap once it's available in ExtCore.
    Follow : TagMap<NonterminalIndexTag, TagSet<TerminalIndexTag>>;
    //
    Nullable : TagMap<NonterminalIndexTag, bool>;
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
    let internal nullable (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>) =
        /// Implementation of the nullable-map-computing algorithm.
        let rec computeNullable (nullable : TagMap<NonterminalIndexTag, bool>) =
            let nullable, updated =
                ((nullable, false), taggedGrammar.ProductionsByNonterminal)
                ||> TagMap.fold (fun (nullable, updated) nonterminalIndex nonterminalProductions ->
                    // If this nonterminal is already known to be nullable, skip it.
                    if TagMap.find nonterminalIndex nullable then
                        nullable, updated
                    else
                        /// When set, denotes that this nonterminal is nullable.
                        let isNullable =
                            nonterminalProductions
                            |> TagSet.exists (fun ruleIndex ->
                                taggedGrammar.Productions
                                |> TagMap.find ruleIndex
                                |> Array.forall (function
                                    | Symbol.Terminal _ ->
                                        false
                                    | Symbol.Nonterminal nonterminalIndex ->
                                        TagMap.find nonterminalIndex nullable))

                        // If this nonterminal is nullable, update its entry in the map.
                        if isNullable then
                            TagMap.add nonterminalIndex true nullable,
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

        // OPTIMIZE : Use TagBimap.toMap here instead -- it's O(1) --
        // then call TagMap.map to map the value to false.
        (TagMap.empty, taggedGrammar.Nonterminals)
        ||> TagBimap.fold (fun initialMap nonterminalIndex _ ->
            TagMap.add nonterminalIndex false initialMap)
        |> computeNullable

    /// Determines if all symbols within the specified slice of a production are nullable.
    let inline internal allNullableInSlice (production : TaggedProductionRule, startInclusive, endInclusive, nullable : TagMap<NonterminalIndexTag, bool>) =
        (startInclusive, endInclusive)
        ||> Range.forall (fun index ->
            match production.[index] with
            | Symbol.Terminal _ ->
                false
            | Symbol.Nonterminal nonterminalIndex ->
                TagMap.find nonterminalIndex nullable)

    //
    let internal first (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>) (nullable : TagMap<NonterminalIndexTag, bool>) =
        /// Implementation of the algorithm for computing the FIRST sets of the nonterminals.
        let rec computeFirst (firstSets : TagMap<NonterminalIndexTag, TagSet<TerminalIndexTag>>) =
            let firstSets, updated =
                ((firstSets, false), taggedGrammar.ProductionsByNonterminal)
                ||> TagMap.fold (fun (firstSets, updated) nonterminal nonterminalProductions ->
                    ((firstSets, updated), nonterminalProductions)
                    ||> TagSet.fold (fun (firstSets, updated) ruleIndex ->
                        let taggedProduction = TagMap.find ruleIndex taggedGrammar.Productions

                        let mutable firstSets = firstSets
                        let mutable updated = updated

                        for i = 0 to Array.length taggedProduction - 1 do
                            if i = 0 || allNullableInSlice (taggedProduction, 0, i - 1, nullable) then
                                /// The FIRST set for the current nonterminal.
                                let nontermFirstSet = TagMap.find nonterminal firstSets
                                
                                /// The updated FIRST set for the current nonterminal.
                                let nontermFirstSet' =
                                    /// The FIRST set for the i-th symbol in the production.
                                    let symbolFirstSet =
                                        match taggedProduction.[i] with
                                        | Symbol.Terminal terminalIndex ->
                                            TagSet.singleton terminalIndex
                                        | Symbol.Nonterminal nonterminalIndex ->
                                            TagMap.find nonterminalIndex firstSets
                                    
                                    TagSet.union nontermFirstSet symbolFirstSet

                                // Set the 'updated' flag iff the nonterminal's FIRST set
                                // was actually changed.
                                if nontermFirstSet <> nontermFirstSet' then
                                    updated <- true
                                    firstSets <- TagMap.add nonterminal nontermFirstSet' firstSets

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

        // OPTIMIZE : Use TagBimap.toMap here instead -- it's O(1) --
        // then call TagMap.map to map the value to TagSet.empty.
        (TagMap.empty, taggedGrammar.Nonterminals)
        ||> TagBimap.fold (fun initialMap nonterminalIndex _ ->
            TagMap.add nonterminalIndex TagSet.empty initialMap)
        |> computeFirst

    //
    let internal follow (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>)
        (nullable : TagMap<NonterminalIndexTag, bool>) (firstSets : TagMap<NonterminalIndexTag, TagSet<TerminalIndexTag>>) =
        /// Implementation of the algorithm for computing the FOLLOW sets of the nonterminals.
        let rec computeFollow (followSets : TagMap<NonterminalIndexTag, TagSet<TerminalIndexTag>>) =
            let followSets, updated =
                ((followSets, false), taggedGrammar.ProductionsByNonterminal)
                ||> TagMap.fold (fun (followSets, updated) nonterminalIndex nonterminalProductions ->
                    ((followSets, updated), nonterminalProductions)
                    ||> TagSet.fold (fun (followSets, updated) ruleIndex ->
                        let taggedProduction = TagMap.find ruleIndex taggedGrammar.Productions

                        let mutable followSets = followSets
                        let mutable updated = updated

                        let productionLength = Array.length taggedProduction
                        for i = 0 to productionLength - 1 do
                            // Only compute follow sets for non-terminals!
                            match taggedProduction.[i] with
                            | Symbol.Terminal _ -> ()
                            | Symbol.Nonterminal ithSymbolNontermId ->                            
                                // If this nonterminal is the last symbol in the production, or all of the symbols
                                // which follow it are nullable (i.e., they could all be empty), then the FOLLOW set
                                // of this nonterminal must contain the FOLLOW set of the nonterminal producing this production.
                                if i = productionLength - 1 ||
                                    allNullableInSlice (taggedProduction, i + 1, productionLength - 1, nullable) then
                                    /// The FOLLOW set for the i-th symbol in the production.
                                    let ithSymbolFollowSet = TagMap.find ithSymbolNontermId followSets

                                    /// The updated FOLLOW set for the i-th symbol in the production.
                                    let ithSymbolFollowSet' =
                                        /// The FOLLOW set for the current nonterminal.
                                        let nontermFollowSet = TagMap.find nonterminalIndex followSets
                                        // Merge it with the FOLLOW set for the i-th symbol.
                                        TagSet.union ithSymbolFollowSet nontermFollowSet

                                    // Set the 'updated' flag iff the i-th symbol's FOLLOW set
                                    // was actually changed.
                                    if ithSymbolFollowSet <> ithSymbolFollowSet' then
                                        updated <- true
                                        followSets <- TagMap.add ithSymbolNontermId ithSymbolFollowSet' followSets

                                // If there are any non-nullable symbols in the production which follow the i-th symbol,
                                // then merge the FIRST set of the first of those non-nullable symbols into the FOLLOW set
                                // of the i-th symbol; also merge the FIRST sets of any nullable symbols which appear
                                // prior to the first non-nullable symbol.
                                for j = i + 1 to productionLength - 1 do
                                    if i + 1 = j || allNullableInSlice (taggedProduction, i + 1, j - 1, nullable) then
                                        /// The FOLLOW set for the i-th symbol in the production.
                                        let ithSymbolFollowSet = TagMap.find ithSymbolNontermId followSets

                                        /// The updated FOLLOW set for the i-th symbol in the production.
                                        let ithSymbolFollowSet' =
                                            /// The FIRST set for the j-th symbol in the production.
                                            let jthSymbolFirstSet =
                                                match taggedProduction.[j] with
                                                | Symbol.Terminal terminalIndex ->
                                                    TagSet.singleton terminalIndex
                                                | Symbol.Nonterminal nonterminalIndex ->
                                                    TagMap.find nonterminalIndex firstSets

                                            TagSet.union ithSymbolFollowSet jthSymbolFirstSet

                                        // Set the 'updated' flag iff the i-th symbol's FOLLOW set
                                        // was actually changed.
                                        if ithSymbolFollowSet <> ithSymbolFollowSet' then
                                            updated <- true
                                            followSets <- TagMap.add ithSymbolNontermId ithSymbolFollowSet' followSets

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

        (TagMap.empty, taggedGrammar.Nonterminals)
        ||> TagBimap.fold (fun initialMap nonterminalIndex nonterminal ->
            let initialSet =
                match nonterminal with
                | AugmentedNonterminal.Start ->
                    // The FOLLOW set for the augmented start symbol
                    // is initialized with the end-of-file marker.
                    taggedGrammar.Terminals
                    |> TagBimap.findValue EndOfFile
                    |> TagSet.singleton
                | AugmentedNonterminal.Nonterminal _ ->
                    TagSet.empty
            TagMap.add nonterminalIndex initialSet initialMap)
        |> computeFollow

    //
    let ofGrammar (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>) =
        /// Map denoting which nonterminals in the grammar are nullable.
        let nullable = nullable taggedGrammar

        /// The FIRST sets for the nonterminals in the grammar.
        let firstSets = first taggedGrammar nullable

        /// The FOLLOW sets for the nonterminals in the grammar.
        let followSets = follow taggedGrammar nullable firstSets

        // Combine the computed sets into a PredictiveSets record and return it.
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

