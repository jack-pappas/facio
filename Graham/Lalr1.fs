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

namespace Graham.LR

open System.Diagnostics
open Graham
open AugmentedPatterns
open Graham.Analysis
open Graham.Graph


/// <summary>LALR(1) parser table generator.</summary>
/// <remarks>Look-Ahead LR(1) (LALR(1)) parsing is a simplified form of LR(1) parsing;
/// it has "just enough" power to parse most languages while avoiding the huge
/// tables associated with canonical LR(1) parsers. A LALR(1) parser table has the
/// the same number of parser states (table rows) as an LR(0) or SLR(1) parser table
/// for the same grammar; the only difference is that the LALR(1) algorithm is able
/// to resolve more conflicts automatically than SLR(1) by using a more powerful algorithm
/// for computing lookaheads.</remarks>
[<RequireQualifiedAccess>]
module Lalr1 =
    module Graph = VertexLabeledSparseDigraph

    /// Computes the "direct read symbols" for each nonterminal transition; that is, it computes the set
    /// of terminals which label the out-edges of the state targeted by a nonterminal transition.
    let private directRead (lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>) =
        (Map.empty, lr0ParserTable.GotoTable)
        ||> Map.fold (fun directRead transition succStateId ->
            // OPTIMIZE : Use a different data structure for the GOTO and ACTION tables
            // so this can be made into a simple lookup instead of having to traverse the ACTION table repeatedly.
            let directReadSymbols =
                (Set.empty, lr0ParserTable.ActionTable)
                ||> Map.fold (fun directReadSymbols (stateId, terminal) entry ->
                    if stateId = succStateId &&
                       (match entry with
                        | Action Accept
                        | Action (Shift _)
                        | Conflict { Shift = Some _; } -> true
                        | _ -> false) then
                        Set.add terminal directReadSymbols
                    else
                        directReadSymbols)

            // Add the direct read symbols for this transition into the map.
            Map.add transition directReadSymbols directRead)

    // D. Compute 'Read' using the SCC-based transitive closure algorithm.
    // If a cycle is detected, announce that the grammar is not LR(k) for any 'k'.
    let private read (lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>) nonterminalTransitions nullable =
        // B. Initialize 'Read' to DR. One set for each nonterminal transition,
        // by inspection of the transition's successor state.
        let directRead = directRead lr0ParserTable

        // C. Compute 'reads'. One set of nonterminal transitions per nonterminal transition,
        // by inspection of the successor state of the later transition.
        let reads =
            (Map.empty, lr0ParserTable.GotoTable)
            ||> Map.fold (fun reads transition succStateId ->
                (reads, lr0ParserTable.GotoTable)
                ||> Map.fold (fun reads ((stateId, nonterminalIndex) as succTransition) _ ->
                    // We only care about successors of the original transition;
                    // also, the nonterminal for this (successor) transition must be nullable.
                    if stateId = succStateId &&
                        TagMap.find nonterminalIndex nullable then
                        // Add the edge to the adjacency map representing the induced 'reads' graph.
                        let readsTransition =
                            match Map.tryFind transition reads with
                            | None ->
                                Set.singleton succTransition
                            | Some readsTransition ->
                                Set.add succTransition readsTransition

                        Map.add transition readsTransition reads
                    else
                        reads))

        //
        Relation.digraph (nonterminalTransitions, reads, directRead)

    /// Compute the 'includes' and 'lookback' relations needed to compute the look-ahead sets for a grammar.
    let private lookbackAndIncludes (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>)
                                    (lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>)
                                    (nonterminalTransitions : Set<NonterminalTransition>)
                                    (nullable : TagMap<NonterminalIndexTag, bool>) =
        ((PartialFunction.empty, Relation.empty), nonterminalTransitions)
        ||> Set.fold (fun lookback_includes (stateId, nonterminalIndex) ->
            //
            let parserState = TagBimap.find stateId lr0ParserTable.ParserStates

            // Fold over the LR(0) items in this parser state.
            (lookback_includes, parserState)
            ||> Set.fold (fun (lookback : PartialFunction<_, NonterminalTransition>, includes : Relation<_>) item ->
                // Only consider items with rules which produce this nonterminal.
                let itemNonterminalIndex = TagMap.find item.ProductionRuleIndex taggedGrammar.NonterminalOfProduction
                if itemNonterminalIndex <> nonterminalIndex then
                    lookback, includes
                else
                    /// The production of this item.
                    let itemProduction = TagMap.find item.ProductionRuleIndex taggedGrammar.Productions

                    // Add edges to the 'includes' relation graph.
                    let includes, j =
                        (int item.Position, Array.length itemProduction - 1, (includes, stateId))
                        |||> Range.fold (fun (includes, j) position ->
                            let t = itemProduction.[position]
                            let includes =
                                // Only care about nonterminal transitions here
                                match t with
                                | Symbol.Terminal _ ->
                                    includes
                                | Symbol.Nonterminal t ->
                                    if Set.contains (j, t) nonterminalTransitions &&
                                        // At this point, we just need to check if the rest of the
                                        // right context of the production is nullable; if so, then
                                        // we can add the edge to the 'includes' graph.
                                        PredictiveSets.allNullableInSlice (itemProduction, position + 1, Array.length itemProduction - 1, nullable) then
                                            Relation.add (j, t) (stateId, nonterminalIndex) includes
                                    else
                                        includes

                            let j =
                                match t with
                                | Symbol.Terminal t ->
                                    lr0ParserTable.ActionTable
                                    |> Map.tryFind (j, t)
                                    |> Option.bind (function
                                        // If this entry contains a Shift action,
                                        // retrieve the target state from it.
                                        | Action (Shift shiftTarget)
                                        | Conflict { Shift = Some shiftTarget; } ->
                                            Some shiftTarget
                                        | _ ->
                                            None)
                                | Symbol.Nonterminal t ->
                                    lr0ParserTable.GotoTable
                                    |> Map.tryFind (j, t)

                            // TODO : For safety and clarity, change this fold to use an F# option
                            // instead of representing the 'invalid' state as -1.
                            let j = defaultArg j -1<_>
                            includes, j)

                    // Add edges to the 'lookback' relation.
                    let lookback : PartialFunction<_,_> =
                        if j = -1<_> then
                            lookback
                        else
                            // 'j' represents the final/last state of the path through the parser transition graph
                            // which describes the derivation of a rule (thereby producing a nonterminal).
                            let rule = itemNonterminalIndex, item.ProductionRuleIndex
                            (lookback, TagBimap.find j lr0ParserTable.ParserStates)
                            ||> Set.fold (fun lookback item' ->
                                //if item.Nonterminal = item'.Nonterminal
                                //    && item.Production = item'.Production then
                                if item.ProductionRuleIndex = item'.ProductionRuleIndex then
                                    PartialFunction.add (j, rule) (stateId, nonterminalIndex) lookback
                                else
                                    lookback)

                    // Pass 'lookback' and 'includes' through to the next iteration.
                    lookback, includes))

    (*  TODO :  Modify the 'lookaheadSets' function to accept another parameter specifying the
                ambiguous LR(0) states (i.e., the states which need the LA sets in order to
                resolve their conflicts). By only computing the LA sets which are actually needed,
                the number of set-union operations is greatly reduced -- leading to improved
                average-case performance. This optimization can be further leveraged by upgrading
                the LR(0) parser table to SLR(1) before upgrading to LALR(1); the upgrade to
                SLR(1) will resolve many/most conflicts so we'll only need to compute LA sets
                for the remaining states. *)

    /// Computes the LALR(1) look-ahead (LA) sets given a grammar and its LR(0) parser table.
    let lookaheadSets (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>)
        (lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>) : Choice<Map<_,_>, string> =
        (* DeRemer and Penello's algorithm for computing LALR look-ahead sets. *)

        /// Denotes which nonterminals are nullable.
        let nullable = PredictiveSets.nullable taggedGrammar

        /// The set of nonterminal transitions in the LR(0) parser table (i.e., the GOTO table).
        let nonterminalTransitions =
            (Set.empty, lr0ParserTable.GotoTable)
            ||> Map.fold (fun nonterminalTransitions transition _ ->
                Set.add transition nonterminalTransitions)

        // D. Compute 'Read' using the SCC-based transitive closure algorithm.
        // If a cycle is detected, announce that the grammar is not LR(k) for any 'k'.
        // TODO : Implement cycle detection.
        let Read = read lr0ParserTable nonterminalTransitions nullable

        // E. Compute 'includes' and 'lookback': one set of nonterminal transitions per
        // nonterminal transition and reduction, respectively, by inspection of each nonterminal
        // transition and the associated production right parts, and by considering
        // nullable nonterminals appropriately.
        let lookback, includes =
            lookbackAndIncludes taggedGrammar lr0ParserTable nonterminalTransitions nullable

        // F. Compute the transitive closure of the 'includes' relation (via the SCC algorithm)
        // to compute 'Follow'. Use the same sets as initialized in part B and completed in part D,
        // both as initial values and as workspace. If a cycle is detected in which a Read set
        // is non-empty, announce that the grammar is not LR(k) for any 'k'.
        let Follow =
            // TODO : Fix this so it returns an error if the grammar is not LR(k).
            Relation.digraph (nonterminalTransitions, includes, Read)

        // G. Union the Follow sets to form the LA sets according
        // to the 'lookback' links computed in part F.
        lookback
        |> Map.map (fun _ transitions ->
            (Set.empty, transitions)
            ||> Set.fold (fun lookaheadTokens transition ->
                Map.find transition Follow
                |> Set.union lookaheadTokens))
        |> Choice1Of2

    /// Creates an LALR(1) parser table from a grammar, it's LR(0) or SLR(1) parser table,
    /// and the LALR(1) look-ahead sets computed from the grammar and parser table.
    let upgrade (taggedGrammar : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType>)
        (lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>) lookaheadSets predictiveSets
        : Lr0ParserTable<'Nonterminal, 'Terminal> =
        /// The predictive sets of the grammar.
        // OPTIMIZE : Don't recompute these -- if they've already been computed for SLR(1),
        // we should pass those in instead of recomputing them.
        let predictiveSets =
            predictiveSets
            |> Option.fillWith (fun () ->
                PredictiveSets.ofGrammar taggedGrammar)

        // Use the LALR(1) lookahead sets to resolve conflicts in the LR(0) parser table.
        (lr0ParserTable, lr0ParserTable.ParserStates)
        ||> TagBimap.fold (fun lr0ParserTable stateId items ->
            (lr0ParserTable, items)
            ||> Set.fold (fun lr0ParserTable item ->
                // If the parser position is at the end of this item's production,
                // remove the Reduce actions from the ACTION table for any terminals
                // which aren't in this state/rule's lookahead set.
                let production = TagMap.find item.ProductionRuleIndex taggedGrammar.Productions
                if int item.Position < Array.length production then
                    lr0ParserTable
                else
                    /// This state/rule's look-ahead set.
                    let lookahead =
                        let nonterminalIndex = TagMap.find item.ProductionRuleIndex taggedGrammar.NonterminalOfProduction
                        Map.find (stateId, (nonterminalIndex, item.ProductionRuleIndex)) lookaheadSets

                    // Remove the unnecessary Reduce actions, thereby resolving some conflicts.
                    let action = LrParserAction.Reduce item.ProductionRuleIndex

                    (lr0ParserTable, taggedGrammar.Terminals)
                    ||> TagBimap.fold (fun lr0ParserTable terminalIndex _ ->
                        // Is this terminal in this state/rule's lookahead set?
                        if Set.contains terminalIndex lookahead then
                            lr0ParserTable
                        else
                            // Remove the unnecessary Reduce action for this terminal.
                            let key = stateId, terminalIndex
                            LrParserTable.RemoveAction (lr0ParserTable, key, action))
                        ))

