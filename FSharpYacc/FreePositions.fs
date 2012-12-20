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
open FSharpYacc.LR


/// An immutable implementation of a vertex-labeled sparse digraph.
type private VertexLabeledSparseDigraph<[<EqualityConditionalOn>]'Vertex when 'Vertex : comparison>
        private (vertices : Set<'Vertex>, edges : Set<'Vertex * 'Vertex>) =
    //
    static member internal Empty
        with get () = VertexLabeledSparseDigraph<'Vertex> (Set.empty, Set.empty)

    //
    member __.IsEmpty
        with get () = Set.isEmpty vertices

    //
    member __.Edges
        with get () = edges
    
    //
    member __.Vertices
        with get () = vertices

    //
    member __.ContainsVertex (vertex : 'Vertex) =
        Set.contains vertex vertices

    //
    member __.ContainsEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertices then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertices then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        Set.contains (source, target) edges

    //
    member __.AddVertex (vertex : 'Vertex) =
        VertexLabeledSparseDigraph (
            Set.add vertex vertices,
            edges)

    //
    member __.AddEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertices then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertices then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        VertexLabeledSparseDigraph (
            vertices,
            Set.add (source, target) edges)

    //
    member __.RemoveVertex (vertex : 'Vertex) =
        // Preconditions
        if not <| Set.contains vertex vertices then
            invalidArg "vertex" "The vertex is not in the graph's vertex-set."

        // Remove in- and out-edges of the vertex.
        let edges =
            edges
            |> Set.filter (fun (source, target) ->
                source <> vertex
                && target <> vertex)

        VertexLabeledSparseDigraph (
            Set.remove vertex vertices,
            edges)

    //
    member __.RemoveEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertices then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertices then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        VertexLabeledSparseDigraph (
            vertices,
            Set.remove (source, target) edges)

/// Functions on VertexLabeledSparseDigraphs.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private VertexLabeledSparseDigraph =
    /// The empty graph.
    [<GeneralizableValue>]
    let empty<'Vertex when 'Vertex : comparison> =
        VertexLabeledSparseDigraph<'Vertex>.Empty

    /// Determines if the graph is empty -- i.e., if it's vertex set is empty.
    let inline isEmpty (graph : VertexLabeledSparseDigraph<'Vertex>) =
        graph.IsEmpty

    //
    let inline addVertex (vertex : 'Vertex) (graph : VertexLabeledSparseDigraph<'Vertex>) =
        graph.AddVertex vertex

    //
    let inline addEdge source target (graph : VertexLabeledSparseDigraph<'Vertex>) =
        graph.AddEdge (source, target)

    //
    let inline removeVertex (vertex : 'Vertex) (graph : VertexLabeledSparseDigraph<'Vertex>) =
        graph.RemoveVertex vertex

    //
    let inline removeEdge source target (graph : VertexLabeledSparseDigraph<'Vertex>) =
        graph.RemoveEdge (source, target)

    //
    let inline containsVertex (vertex : 'Vertex) (graph : VertexLabeledSparseDigraph<'Vertex>) =
        graph.ContainsVertex vertex

    //
    let inline containsEdge source target (graph : VertexLabeledSparseDigraph<'Vertex>) =
        graph.ContainsEdge (source, target)

    //
    let dominators (graph : VertexLabeledSparseDigraph<'Vertex>) : Map<'Vertex, Set<'Vertex>> =
        // Find the root vertex.
        let root =
            let roots =
                // Determine which vertices have no incoming edges.
                (graph.Vertices, graph.Edges)
                ||> Set.fold (fun possibleRoots (_, target) ->
                    Set.remove target possibleRoots)

            // The set should have only one root vertex.
            match Set.count roots with
            | 0 ->
                invalidArg "graph" "The graph is empty, or otherwise contains no root vertices."
            | 1 ->
                Set.minElement roots
            | n ->
                invalidArg "graph" "The graph contains multiple components (i.e., the graph is not connected)."

        /// The predecessors of each vertex.
        let predecessorsOf =
            let initialPreds =
                (Map.empty, graph.Vertices)
                ||> Set.fold (fun initialMap vertex ->
                    Map.add vertex Set.empty initialMap)

            (initialPreds, graph.Edges)
            ||> Set.fold (fun predecessorsOf (source, target) ->
                let predsOfTarget =
                    Map.find target predecessorsOf
                    // Add the source vertex to the predecessor set of target.
                    |> Set.add source

                // Add the updated set to the map.
                Map.add target predsOfTarget predecessorsOf)

        /// The graph vertices, excluding the root vertex.
        let vertices = Set.remove root graph.Vertices
            
        /// Uses a worklist-style algorithm to iteratively remove non-dominators
        /// from the dominator sets of the vertices until a fixpoint is reached.
        let rec domFix dominatedBy =
            let modified, dominatedBy =
                ((false, dominatedBy), vertices)
                ||> Set.fold (fun (modified, dominatedBy) vertex ->
                    //
                    let vertexDominators' =                    
                        // Intersect the dominator sets of the predecessors of this vertex.
                        (graph.Vertices, Map.find vertex predecessorsOf)
                        ||> Set.fold (fun predDoms predVertex ->
                            Map.find predVertex dominatedBy
                            |> Set.intersect predDoms)
                        // Add the vertex itself to the result.
                        |> Set.add vertex

                    // If the new set of dominators for this vertex is different
                    // than the existing set, set the modified flag and update this
                    // vertex's entry in the map.
                    let vertexDominators = Map.find vertex dominatedBy
                    if vertexDominators <> vertexDominators' then
                        true, Map.add vertex vertexDominators' dominatedBy
                    else
                        modified, dominatedBy)

            // If any of the sets were modified, keep iterating.
            if modified then
                domFix dominatedBy
            else
                dominatedBy

        // For vertices other than the root, initialize their
        // dominator sets to the graph's vertex-set.
        (Map.empty, vertices)
        ||> Set.fold (fun dominatedBy vertex ->
            Map.add vertex graph.Vertices dominatedBy)
        // The root vertex is it's own dominator.
        |> Map.add root (Set.singleton root)
        // Find the dominator sets by finding a fixpoint of the set equations.
        |> domFix

    /// Computes the set of vertices reachable from each vertex in a graph.
    let reachable (graph : VertexLabeledSparseDigraph<'Vertex>) =
        // This is a simplified version of the Floyd-Warshall algorithm
        // which checks only for reachability (Warshall's algorithm).
        let vertices = graph.Vertices

        /// The initial map, containing an empty reachable-set for each vertex.
        // NOTE : This is primarily to ensure that the map contains an entry
        // for each vertex; it also avoids a branch in the innermost loop.
        let initialMap =
            (Map.empty, vertices)
            ||> Set.fold (fun initialMap vertex ->
                Map.add vertex Set.empty initialMap)

        (initialMap, vertices)
        ||> Set.fold (fun reachableFrom k ->
            (reachableFrom, vertices)
            ||> Set.fold (fun reachableFrom i ->
                (reachableFrom, vertices)
                ||> Set.fold (fun reachableFrom j ->
                    // If there's an edge i->k and k->j, then add the edge i->j.
                    if containsEdge i k graph && containsEdge k j graph then
                        /// The set of vertices reachable from 'i'.
                        let ``reachable from i`` =
                            Map.find i reachableFrom
                            // Add 'j' to the set of vertices reachable from 'i'
                            |> Set.add j

                        // Update the map entry for 'i' with the result.
                        Map.add i ``reachable from i`` reachableFrom
                    else
                        // Keep looping without modifying the set.
                        reachableFrom)))

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
    let private positionGraphs (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) =
        //
        let lr0ParserTable = Lr0.createTable grammar

        // Compute the Parser State Position Graph for each parser state.
        (Map.empty, lr0ParserTable.ParserStates)
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
        let dominated = Graph.dominators graph

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
        // Compute the parser state position graphs of the LR(0) parser states of the augmented grammar.
        let positionGraphs = positionGraphs grammar

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
