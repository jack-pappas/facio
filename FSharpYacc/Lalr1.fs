(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace FSharpYacc.LR

open LanguagePrimitives
open FSharpYacc.Grammar
open AugmentedPatterns
open FSharpYacc.Analysis
open FSharpYacc.Graph


/// An LALR(1) item.
type internal Lalr1Item<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrItem<'Nonterminal, 'Terminal, Set<'Terminal>>

/// An LALR(1) parser state -- i.e., a set of LR(1) items.
type internal Lalr1ParserState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrParserState<'Nonterminal, 'Terminal, Set<'Terminal>>

/// LALR(1) parser table generation state.
type internal Lalr1TableGenState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrTableGenState<'Nonterminal, 'Terminal, Set<'Terminal>>

/// An LALR(1) parser table.
type Lalr1ParserTable<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrParserTable<
        AugmentedNonterminal<'Nonterminal>,
        AugmentedTerminal<'Terminal>,
        Set<AugmentedTerminal<'Terminal>>>

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
                ||> Map.fold (fun directReadSymbols (stateId, terminal) _ ->
                    if stateId = succStateId then
                        Set.add terminal directReadSymbols
                    else
                        directReadSymbols)

            // Add the direct read symbols for this transition into the map.
            Map.add transition directReadSymbols directRead)

    // D. Compute 'Read' using the SCC-based transitive closure algorithm.
    // If a cycle is detected, announce that the grammar is not LR(k) for any 'k'.
    let private read (lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>, nonterminalTransitions, nullable) =
        // B. Initialize 'Read' to DR. One set for each nonterminal transition,
        // by inspection of the transition's successor state.
        let directRead = directRead lr0ParserTable

        // Add the nonterminal transitions to the graph.
        let reads =
            (Graph.empty, nonterminalTransitions)
            ||> Set.fold (fun reads transition ->
                Graph.addVertex transition reads)

        // C. Compute 'reads'. One set of nonterminal transitions per nonterminal transition,
        // by inspection of the successor state of the later transition.
        (reads, lr0ParserTable.GotoTable)
        ||> Map.fold (fun reads transition succStateId ->
            (reads, lr0ParserTable.GotoTable)
            ||> Map.fold (fun reads ((stateId, nonterminal) as succTransition) _ ->
                // We only care about successors of the original transition;
                // also, the nonterminal for this (successor) transition must be nullable.
                if stateId = succStateId &&
                    Map.find nonterminal nullable then
                    // Add the edge to the 'reads' graph.
                    Graph.addEdge transition succTransition reads
                else
                    reads))
        //
        |> Graph.reachable
        //
        |> Map.map (fun transition reachableTransitions ->
            /// The direct-read (DR) set for this transition.
            let transitionDirectRead = Map.find transition directRead

            // Union the DR set for this transition with the DR sets
            // of any other transitions reachable via the 'reads' relation.
            (transitionDirectRead, reachableTransitions)
            ||> Set.fold (fun read reachableTransition ->
                Map.find reachableTransition directRead
                |> Set.union read))

    //
    let private includes (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>, lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>, nonterminalTransitions, nullable) =
        ((Graph.empty, Graph.empty), nonterminalTransitions)
        ||> Set.fold (fun lookback_includes (stateId, nonterminal) ->
            //
            let parserState = Map.find stateId lr0ParserTable.ParserStates

            // Fold over the LR(0) items in this parser state.
            (lookback_includes, parserState)
            ||> Set.fold (fun (lookback, includes) item ->
                // Only consider items with rules which produce this nonterminal.
                if item.Nonterminal <> nonterminal then
                    lookback, includes
                else
                    let includes, j =
                        let rhsPositions = seq {
                            int item.Position .. Array.length item.Production - 1 }
                        ((includes, stateId), rhsPositions)
                        ||> Seq.fold (fun (includes, j) position ->
                            let t = item.Production.[position]
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
                                        PredictiveSets.allNullableInSlice (item.Production, position + 1, Array.length item.Production - 1, nullable) then
                                            Graph.addEdgeAndVertices (stateId, nonterminal) (j, t) includes
                                    else
                                        includes

                            let j =
                                match t with
                                | Symbol.Terminal t ->
                                    lr0ParserTable.ActionTable
                                    |> Map.tryFind (j, t)
                                    |> Option.bind (fun actions ->
                                        // There can be at most one (1) Shift action in each set
                                        // of actions; if this set contains a Shift action,
                                        // get the 'target' state from it.
                                        (None, actions)
                                        ||> Set.fold (fun shift action ->
                                            match action with
                                            | Shift target ->
                                                Some target
                                            | _ -> shift))
                                | Symbol.Nonterminal t ->
                                    lr0ParserTable.GotoTable
                                    |> Map.tryFind (j, t)

                            let j = defaultArg j -1<_>
                            includes, j)
                
                    lookback, includes))

    //
    let ofLr0Table (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>, lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>)
        : Choice<Lr0ParserTable<'Nonterminal, 'Terminal>, string> =
        (* DeRemer and Penello's algorithm for computing LALR look-ahead sets. *)

        /// Denotes which nonterminals are nullable.
        let nullable = FSharpYacc.Analysis.PredictiveSets.computeNullable grammar.Productions

        /// The set of nonterminal transitions in the LR(0) parser table (i.e., the GOTO table).
        let nonterminalTransitions =
            (Set.empty, lr0ParserTable.GotoTable)
            ||> Map.fold (fun nonterminalTransitions transition _ ->
                Set.add transition nonterminalTransitions)

        // D. Compute 'Read' using the SCC-based transitive closure algorithm.
        // If a cycle is detected, announce that the grammar is not LR(k) for any 'k'.
        let Read = read (lr0ParserTable, nonterminalTransitions, nullable)

        // E. Compute 'includes' and 'lookback': one set of nonterminal transitions per
        // nonterminal transition and reduction, respectively, by inspection of each nonterminal
        // transition and the associated production right parts, and by considering
        // nullable nonterminals appropriately.
        let includes = includes (grammar, lr0ParserTable, nonterminalTransitions, nullable)

        // F. Compute the transitive closure of the 'includes' relation (via the SCC algorithm)
        // to compute 'Follow'. Use the same sets as initialized in part B and completed in part D,
        // both as initial values and as workspace. If a cycle is detected in which a Read set
        // is non-empty, announce that the grammar is not LR(k) for any 'k'.
        // TODO

        // G. Union the Follow sets to form the LA sets according
        // to the 'lookback' links computed in part F.
        // TODO

        // H. Check for conflicts; if there are none, the grammar is LALR(1).
        // TODO

//        /// Reduce-state/reduce-rule pairs.
//        // OPTIMIZE : Filter this set so it only includes state/rule pairs which are actually causing conflicts.
//        // Most of the pairs in the LR(0) automata should NOT need to be computed, so filtering the set will
//        // greatly reduce the number of calculations which need to be performed.
//        let reduceStateRulePairs =
//            (Set.empty, lr0ParserTable.ParserStates)
//            ||> Map.fold (fun reduceStateRulePairs stateId items ->
//                (reduceStateRulePairs, items)
//                ||> Set.fold (fun reduceStateRulePairs item ->
//                    let productionLength = Array.length item.Production
//                    if int item.Position = productionLength ||                        
//                        (int item.Position = productionLength - 1 &&
//                            item.Production.[productionLength - 1] = (Terminal EndOfFile)) then
//                        Set.add (stateId, (item.Nonterminal, item.Production)) reduceStateRulePairs
//                    else
//                        reduceStateRulePairs))

        //
        raise <| System.NotImplementedException "Lalr1.ofLr0Table"


