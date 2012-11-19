(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpYacc.Derivation

open Ast


//
type GrammarAnalysis<'NonterminalId, 'Token
                    when 'NonterminalId : comparison
                    and 'Token : comparison> = {
    //
    First : Map<'NonterminalId, Set<'Token>>;
    //
    Follow : Map<'NonterminalId, Set<'Token>>;
    //
    Nullable : Map<'NonterminalId, bool>;
    }

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module GrammarAnalysis =
    //
    let internal computeNullable (productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>) =
        /// Implementation of the nullable-map-computing algorithm.
        let rec computeNullable (nullable : Map<'NonterminalId, bool>) =
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
                                | Terminal _ ->
                                    false
                                | Nonterminal nontermId ->
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

    //
    let internal computeFirst (productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>, nullable : Map<'NonterminalId, bool>) =
        /// Implementation of the algorithm for computing the FIRST sets of the nonterminals.
        let rec computeFirst (firstSets : Map<'NonterminalId, Set<'Token>>) =
            let firstSets, updated =
                ((firstSets, false), productions)
                ||> Map.fold (fun (firstSets, updated) nontermId productions ->
                    ((firstSets, updated), productions)
                    ||> Set.fold (fun (firstSets, updated) production ->
                        let mutable firstSets = firstSets
                        let mutable updated = updated

                        for i = 0 to Array.length production - 1 do
                            if i = 0 ||
                                // OPTIMIZE : Array slices are slow -- find another way to implement this.
                                production.[0 .. i - 1]
                                |> Array.forall (function
                                    | Terminal _ ->
                                        false
                                    | Nonterminal nontermId ->
                                        Map.find nontermId nullable) then

                                /// The FIRST set for the current nonterminal.
                                let nontermFirstSet = Map.find nontermId firstSets
                                /// The FIRST set for the i-th symbol in the production.
                                let symbolFirstSet =
                                    match production.[i] with
                                    | Terminal token ->
                                        Set.singleton token
                                    | Nonterminal nontermId ->
                                        Map.find nontermId firstSets

                                /// The updated FIRST set for the current nonterminal.
                                let nontermFirstSet' = Set.union nontermFirstSet symbolFirstSet

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
    let internal computeFollow (productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>,
                                    nullable : Map<'NonterminalId, bool>,
                                    firstSets : Map<'NonterminalId, Set<'Token>>) =
        /// Implementation of the algorithm for computing the FOLLOW sets of the nonterminals.
        let rec computeFollow (followSets : Map<'NonterminalId, Set<'Token>>) =
            let followSets, updated =
                ((followSets, false), productions)
                ||> Map.fold (fun (followSets, updated) nontermId productions ->
                    ((followSets, updated), productions)
                    ||> Set.fold (fun (followSets, updated) production ->
                        let mutable followSets = followSets
                        let mutable updated = updated

                        let k = Array.length production - 1
                        for i = 0 to k do
                            for j = i + 1 to k do
                                if i = k ||
                                    // OPTIMIZE : Array slices are slow -- find another way to implement this.
                                    production.[i + 1 .. k]
                                    |> Array.forall (function
                                        | Terminal _ ->
                                            false
                                        | Nonterminal nontermId ->
                                            Map.find nontermId nullable) then

                                    (* NOTE : At this point, we know the i-th symbol is a nonterminal. *)

                                    /// The nonterminal identifier for the i-th symbol.
                                    let ithSymbolNontermId =
                                        match production.[i] with
                                        | Terminal token ->
                                            failwith "A terminal was found where a nonterminal was expected."
                                        | Nonterminal nontermId ->
                                            nontermId

                                    /// The FOLLOW set for the i-th symbol in the production.
                                    let ithSymbolFollowSet = Map.find ithSymbolNontermId followSets

                                    /// The updated FOLLOW set for the i-th symbol in the production.
                                    let ithSymbolFollowSet' =
                                        /// The FOLLOW set for the current nonterminal.
                                        let nontermFollowSet = Map.find nontermId followSets

                                        Set.union ithSymbolFollowSet nontermFollowSet

                                    // Set the 'updated' flag iff the i-th symbol's FOLLOW set
                                    // was actually changed.
                                    if ithSymbolFollowSet <> ithSymbolFollowSet' then
                                        updated <- true
                                        followSets <- Map.add ithSymbolNontermId ithSymbolFollowSet' followSets

                                if i + 1 = j ||
                                    // OPTIMIZE : Array slices are slow -- find another way to implement this.
                                    production.[i + 1 .. j - 1]
                                    |> Array.forall (function
                                        | Terminal _ ->
                                            false
                                        | Nonterminal nontermId ->
                                            Map.find nontermId nullable) then
                                    
                                    (* NOTE : At this point, we know both the i-th and j-th symbols are nonterminals. *)

                                    /// The nonterminal identifier for the i-th symbol.
                                    let ithSymbolNontermId =
                                        match production.[i] with
                                        | Terminal token ->
                                            failwith "A terminal was found where a nonterminal was expected."
                                        | Nonterminal nontermId ->
                                            nontermId

                                    /// The FOLLOW set for the i-th symbol in the production.
                                    let ithSymbolFollowSet = Map.find ithSymbolNontermId followSets

                                    /// The updated FOLLOW set for the i-th symbol in the production.
                                    let ithSymbolFollowSet' =
                                        /// The FIRST set for the j-th symbol in the production.
                                        let jthSymbolFirstSet =
                                            /// The nonterminal identifier for the j-th symbol.
                                            let jthSymbolNontermId =
                                                match production.[j] with
                                                | Terminal token ->
                                                    failwith "A terminal was found where a nonterminal was expected."
                                                | Nonterminal nontermId ->
                                                    nontermId

                                            Map.find jthSymbolNontermId firstSets

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
        productions
        |> Map.map (fun _ _ -> Set.empty)
        //
        |> computeFollow

    //
    let ofGrammar (grammar : Grammar<'NonterminalId, 'Token>) : GrammarAnalysis<'NonterminalId, 'Token> =
        /// Map denoting which nonterminals in the grammar are nullable.
        let nullable = computeNullable grammar.Productions

        /// The FIRST sets for the nonterminals in the grammar.
        let firstSets = computeFirst (grammar.Productions, nullable)

        /// The FOLLOW sets for the nonterminals in the grammar.
        let followSets = computeFollow (grammar.Productions, nullable, firstSets)

        // Combine the computed sets into a GrammarAnalysis record and return it.
        { Nullable = nullable;
            First = firstSets;
            Follow = followSets; }

