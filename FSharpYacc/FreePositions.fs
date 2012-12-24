(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace FSharpYacc.Analysis

open LanguagePrimitives
open FSharpYacc.Grammar
open AugmentedPatterns
open FSharpYacc.Graph
open FSharpYacc.LR


//
type internal ParserStatePositionGraphAction<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    /// Shift the specified terminal (token) onto the parser stack.
    | Shift of 'Terminal
    /// Reduce by a production rule.
    // NOTE : When 'Nonterminal is instantiated as AugmentedNonterminal<'Nonterminal>,
    // note that (Reduce Start) is the "Accept" action.
    | Reduce of 'Nonterminal

/// A node in a Parser State Position Graph (PSPG).
type internal ParserStatePositionGraphNode<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> =
    /// An LR(k) item.
    | Item of LrItem<'Nonterminal, 'Terminal, 'Lookahead>
    /// A parser action.
    | Action of ParserStatePositionGraphAction<'Nonterminal, 'Terminal>

/// <summary>A Parser State Position Graph (PSPG).</summary>
/// <remarks>
/// <para>A Parser State Position Graph represents the possible epsilon-moves
/// between the items of a parser state. These graphs are used to classify
/// parser positions as 'free' or 'forbidden'; semantic actions can be
/// safely inserted at a position iff the position is 'free'.</para>
/// <para>The graph is represented as a set of directed edges.</para>
/// </remarks>
type internal ParserStatePositionGraph<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> =
    VertexLabeledSparseDigraph<ParserStatePositionGraphNode<'Nonterminal, 'Terminal, 'Lookahead>>

//
[<RequireQualifiedAccess>]
module internal FreePositions =
    module Graph = VertexLabeledSparseDigraph

    /// Computes the Parser State Position Graph of an LR(0) parser state.
    let private positionGraph (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) (parserState : Lr0ParserState<'Nonterminal, 'Terminal>)
        : ParserStatePositionGraph<_,_,_> =
        // The initial parser state graph.
        // Contains all items in the LR(0) state as vertices,
        // but it is an _empty_ graph (i.e., a graph with an empty edge-set).
        let positionGraph =
            (Graph.empty, parserState)
            ||> Set.fold (fun positionGraph item ->
                // Add the item to the graph.
                Graph.addVertex (Item item) positionGraph)

        (* OPTIMIZE :   The code below can be improved slightly (for correctness
                        and speed) by using our Set.mapPartition function. *)

        //
        let transitionItems, actionItems =
            parserState
            |> Set.partition (fun item ->
                // Does this item represent the derivation of the entire production?
                if int item.Position = Array.length item.Production then
                    false   // Reduce
                else
                    match item.Production.[int item.Position] with
                    | Symbol.Terminal _ -> false    // Shift
                    | Symbol.Nonterminal _ -> true)

        // Add edges representing parser actions to the graph.
        let positionGraph =
            (positionGraph, actionItems)
            ||> Set.fold (fun positionGraph item ->
                if int item.Position = Array.length item.Production then
                    let action = Action <| Reduce item.Nonterminal

                    // Add the action to the graph in case it hasn't been added yet.
                    positionGraph
                    |> Graph.addVertex action
                    // Add an edge from this item to the action.
                    |> Graph.addEdge (Item item) action
                else
                    match item.Production.[int item.Position] with
                    | Symbol.Nonterminal _ ->
                        invalidOp "A transition item was found where an action item was expected."
                    | Symbol.Terminal terminal ->
                        let action = Action <| Shift terminal

                        // Add the action to the graph in case it hasn't been added yet.
                        positionGraph
                        |> Graph.addVertex action
                        // Add an edge from this item to the action.
                        |> Graph.addEdge (Item item) action)

        // Find edges representing derivations of non-terminals and add them to
        // the existing set of graph edges (which may already contain some shift edges).
        (positionGraph, transitionItems)
        ||> Set.fold (fun positionGraph nonterminalDerivingItem ->
            /// The nonterminal being derived by this item.
            let derivingNonterminal =
                match nonterminalDerivingItem.Production.[int nonterminalDerivingItem.Position] with
                | Symbol.Nonterminal nt -> nt
                | Symbol.Terminal _ ->
                    invalidOp "A terminal was found where a nonterminal was expected."

            (positionGraph, parserState)
            ||> Set.fold (fun positionGraph item ->
                // A derivation edge exists iff the nonterminal produced by this item
                // is the one we're trying to derive AND the parser position of this
                // item is the initial position.
                if item.Nonterminal = derivingNonterminal && item.Position = 0<_> then
                    Graph.addEdge (Item nonterminalDerivingItem) (Item item) positionGraph
                else
                    positionGraph))

    //
    let private positionGraphs (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) (parserTable : LrParserTable<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>, unit>) =
        // Compute the Parser State Position Graph for each parser state.
        (Map.empty, parserTable.ParserStates)
        ||> Map.fold (fun parserStatePositionGraphs parserStateId parserState ->
            let pspg = positionGraph grammar.Productions parserState
            Map.add parserStateId pspg parserStatePositionGraphs)

    //
    let allPositions (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) =
        // OPTIMIZE : This function should be rewritten for better performance.
        (Set.empty, grammar.Productions)
        ||> Map.fold (fun positions nonterminal productions ->
            // Handle the start production specially
            match nonterminal with
            | Start ->
                // The EndOfFile token is never shifted by the parser,
                // so the production of the start symbol only has
                // two (2) positions, not three (3).
                positions
                |> Set.add (Start, 0<_>, 0<_>)
                |> Set.add (Start, 0<_>, 1<_>)
            | Nonterminal _ ->
                // Fold over the productions for this nonterminal
                ((positions, (0<_> : ProductionIndex)), productions)
                ||> Array.fold (fun (positions, productionIndex) production ->
                    // Create the positions for this production, then add them to the set of all positions.
                    let productionPositions =
                        let len = Array.length production
                        [| for i in 0 .. len ->
                            nonterminal, productionIndex, ((Int32WithMeasure i) : int<ParserPosition>) |]
                        |> Set.ofArray

                    Set.union positions productionPositions,
                    productionIndex + 1<_>)
                // Discard the production index
                |> fst)

    //
    let private nonfreeItems (graph : ParserStatePositionGraph<'Nonterminal, 'Terminal, 'Lookahead>) =
        /// For each item in the graph, contains the set of items/actions reachable from it.
        let reachableFrom = Graph.reachable graph

        /// For each item in the graph, contains the set of items/actions it dominates.
        let dominated =
            match Graph.dominators graph with
            | Choice1Of2 x -> x
            | Choice2Of2 errorMsg ->
                exn ("This item contains a conflict (S/R or R/R). \
                      Free positions can not be computed until all conflicts are resolved.",
                      exn errorMsg)
                |> raise

        // Positions are not free if they can derive themselves
        // (i.e., if they have a self-loop in the graph).
        let nonfreeItems =
            (Set.empty, reachableFrom)
            ||> Map.fold (fun nonfreeItems itemOrAction reachable ->
                // We only care about items, not actions.
                match itemOrAction with
                | Item item when Set.contains itemOrAction reachable ->
                    Set.add item nonfreeItems
                | _ ->
                    nonfreeItems)

        // For a position to be free, it must be a dominator
        // of every action reachable from it.
        (nonfreeItems, graph.Vertices)
        ||> Set.fold (fun nonfreeItems itemOrAction ->
            match itemOrAction with
            | Action _ ->
                // We only care about items/positions so just ignore actions.
                nonfreeItems
            | Item item ->
                /// The items/actions dominated by this item.
                let dominatedItemsAndActions = Map.find itemOrAction dominated

                /// The items/actions reachable from this item.
                let reachableItemsAndActions = Map.find itemOrAction reachableFrom

                // Does this item dominate all of the actions reachable from it?
                let dominatesAllReachableActions =
                    reachableItemsAndActions
                    |> Set.forall (function
                        | Item _ ->
                            true    // Ignore items here, we only care about actions.
                        | (Action _) as action ->
                            Set.contains action dominatedItemsAndActions)                    
            
                // If not, add this item to the set of non-free items.
                if dominatesAllReachableActions then
                    nonfreeItems
                else
                    Set.add item nonfreeItems)

    //
    let ofAugmentedGrammar (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) =
        //
        let lr0ParserTable = Lr0.createTable grammar

        // Compute the parser state position graphs of the LR(0) parser states of the augmented grammar.
        let positionGraphs = positionGraphs grammar lr0ParserTable

        // Compute the set of non-free (forbidden or contingent) positions in the entire grammar.
        (Set.empty, positionGraphs)
        ||> Map.fold (fun allNonfreeItems _ pspg ->
            // The set of non-free positions in each position graph.
            nonfreeItems pspg
            // Combine the result with the non-free positions
            // of the other states we've already processed.
            |> Set.union allNonfreeItems)
        // TEMP : Convert the non-free items to non-free positions.
        // Eventually, we'll modify the LR table-generating code to use
        // this representation -- then this conversion can be removed.
        |> Set.map (fun nonfreeItem ->
            // Find the index of this production rule.
            let productionIndex : ProductionIndex =
                grammar.Productions
                |> Map.find nonfreeItem.Nonterminal
                |> Array.findIndex ((=) nonfreeItem.Production)
                |> Int32WithMeasure

            // Return a tuple representing this position.
            nonfreeItem.Nonterminal,
            productionIndex,
            nonfreeItem.Position)
        // Compute the set of all positions in the grammar;
        // remove the non-free positions from it to produce
        // a set containing only the free positions of the grammar.
        |> Set.difference (allPositions grammar)
