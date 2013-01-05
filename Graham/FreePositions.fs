(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace Graham.Analysis

open LanguagePrimitives
open Graham.Grammar
open AugmentedPatterns
open Graham.Graph
open Graham.LR


//
[<RequireQualifiedAccess>]
module FreePositions =
    module Graph = VertexLabeledSparseDigraph

    //
    type private StatePositionGraphAction<'Nonterminal, 'Terminal
        when 'Nonterminal : comparison
        and 'Terminal : comparison> =
        /// Shift the specified terminal (token) onto the parser stack.
        | Shift of 'Terminal
        /// Reduce by a production rule.
        // NOTE : When 'Nonterminal is instantiated as AugmentedNonterminal<'Nonterminal>,
        // note that (Reduce Start) is the "Accept" action.
        | Reduce of 'Nonterminal

        /// <inherit />
        override this.ToString () =
            match this with
            | Shift terminal ->
                "Shift " + terminal.ToString ()
            | Reduce nonterminal ->
                "Reduce " + nonterminal.ToString ()

    /// A node in a State Position Graph (PSPG).
    type private StatePositionGraphNode<'Nonterminal, 'Terminal, 'Lookahead
        when 'Nonterminal : comparison
        and 'Terminal : comparison
        and 'Lookahead : comparison> =
        /// <summary>The initial (root) node of the graph.</summary>
        /// <remarks>The Initial node is a pseudo-node, but is important because
        /// it ensures the graph is always connected (a necessary condition for
        /// some calculations we perform on the graph).
        | Initial
        /// An LR(k) item.
        | Item of LrItem<'Nonterminal, 'Terminal, 'Lookahead>
        /// A parser action.
        | Action of StatePositionGraphAction<'Nonterminal, 'Terminal>

        /// <inherit />
        override this.ToString () =
            match this with
            | Initial ->
                "Initial"
            | Item item ->
                item.ToString ()
            | Action action ->
                action.ToString ()

    /// <summary>A State Position Graph (SPG).</summary>
    /// <remarks>
    /// <para>A State Position Graph represents the possible epsilon-moves
    /// between the items of a parser state. These graphs are used to classify
    /// parser positions as 'free' or 'forbidden'; semantic actions can be
    /// safely inserted at a position iff the position is 'free'.</para>
    /// <para>The graph is represented as a set of directed edges.</para>
    /// </remarks>
    type private StatePositionGraph<'Nonterminal, 'Terminal, 'Lookahead
        when 'Nonterminal : comparison
        and 'Terminal : comparison
        and 'Lookahead : comparison> =
        VertexLabeledSparseDigraph<StatePositionGraphNode<'Nonterminal, 'Terminal, 'Lookahead>>

    /// Computes the State Position Graph of an LR(0) parser state.
    let private statePositionGraph (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) (parserState : Lr0ParserState<'Nonterminal, 'Terminal>)
        : StatePositionGraph<_,_,_> =
        // The initial state position graph.
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
        let positionGraph =
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

        // Add the Initial (root) node, and add edges from it to any existing root nodes.
        let positionGraph' =
            Graph.addVertex Initial positionGraph

        (positionGraph', Graph.roots positionGraph)
        ||> Set.fold (fun positionGraph root ->
            Graph.addEdge Initial root positionGraph)

    //
    let private statePositionGraphs (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) (parserTable : Lr0ParserTable<'Nonterminal, 'Terminal>) =
        // Compute the State Position Graph for each parser state.
        (Map.empty, parserTable.ParserStates)
        ||> Map.fold (fun statePositionGraphs parserStateId parserState ->
            let spg = statePositionGraph grammar.Productions parserState
            Map.add parserStateId spg statePositionGraphs)

    //
    let allPositions (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) : Set<_> =
        // OPTIMIZE : This function should be rewritten for better performance.
        (((1<_> : ProductionRuleId), Set.empty), grammar.Productions)
        ||> Map.fold (fun (productionRuleId, positions) nonterminal productions ->
            // Handle the start production specially
            match nonterminal with
            | Start ->
                // The EndOfFile token is never shifted by the parser,
                // so the production of the start symbol only has
                // two (2) positions, not three (3).
                productionRuleId + 1<_>,
                positions
                |> Set.add (productionRuleId, 0<_>)
                |> Set.add (productionRuleId, 1<_>)
            | Nonterminal _ ->
                // Fold over the productions for this nonterminal
                productionRuleId + 1<_>,
                (positions, productions)
                ||> Array.fold (fun positions production ->
                    // Create the positions for this production...
                    let len = Array.length production
                    [| for i in 0 .. len ->
                        productionRuleId, ((Int32WithMeasure i) : int<ParserPosition>) |]
                    |> Set.ofArray
                    //  ...then add them to the set of all positions.
                    |> Set.union positions))
        // Discard the production rule counter
        |> snd

    //
    let private nonfreeItems (graph : StatePositionGraph<'Nonterminal, 'Terminal, 'Lookahead>) =
        /// For each item in the graph, contains the set of items/actions reachable from it.
        let reachableFrom = Graph.reachable graph

        /// For each item in the graph, contains the set of items/actions it's dominated _by_.
        let dominatedBy =
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
        ||> Set.fold (fun nonfreeItems node ->
            match node with
            | Initial
            | Action _ ->
                // We only care about items/positions so just ignore actions.
                nonfreeItems
            | Item item ->
                /// The items/actions reachable from this item.
                let reachableItemsAndActions = Map.find node reachableFrom

                // Does this item dominate all of the actions reachable from it?
                let dominatesAllReachableActions =
                    reachableItemsAndActions
                    |> Set.forall (function
                        | Initial
                        | Item _ ->
                            true    // Ignore items here, we only care about actions.
                        | (Action _) as action ->
                            Map.find action dominatedBy
                            |> Set.contains node)                   
            
                // If not, add this item to the set of non-free items.
                if dominatesAllReachableActions then
                    nonfreeItems
                else
                    Set.add item nonfreeItems)

    //
    let ofGrammar (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>, lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>) =
        // Compute the state position graphs of the LR(0) parser states of the augmented grammar.
        let positionGraphs = statePositionGraphs grammar lr0ParserTable

        // TEMP : Only needed until we convert LrItem into a more efficient form (i.e., one that
        // uses the ProductionRuleId instead of the nonterminal, production symbols, etc.)
        /// The production-rule-id lookup table.
        let productionRuleIds =
            (Map.empty, grammar.Productions)
            ||> Map.fold (fun productionRuleIds nonterminal rules ->
                (productionRuleIds, rules)
                ||> Array.fold (fun productionRuleIds ruleRhs ->
                    /// The identifier for this production rule.
                    let productionRuleId : ProductionRuleId =
                        productionRuleIds.Count + 1
                        |> Int32WithMeasure

                    // Add this identifier to the map.
                    Map.add (nonterminal, ruleRhs) productionRuleId productionRuleIds))

        // Compute the set of non-free (forbidden or contingent) positions in the entire grammar.
        (Set.empty, positionGraphs)
        ||> Map.fold (fun allNonfreeItems _ spg ->
            // The set of non-free positions in each position graph.
            nonfreeItems spg
            // Combine the result with the non-free positions
            // of the other states we've already processed.
            |> Set.union allNonfreeItems)
        // TEMP : Convert the non-free items to non-free positions.
        // Eventually, we'll modify the LR table-generating code to use
        // this representation -- then this conversion can be removed.
        |> Set.map (fun nonfreeItem ->
            /// The identifier for this production rule.
            let productionRuleId =
                Map.find (nonfreeItem.Nonterminal, nonfreeItem.Production) productionRuleIds

            // Return a tuple representing this position.
            productionRuleId,
            nonfreeItem.Position)
        // Compute the set of all positions in the grammar;
        // remove the non-free positions from it to produce
        // a set containing only the free positions of the grammar.
        |> Set.difference (allPositions grammar)

    //
    let earliest (freePositions : Set<ProductionRuleId * int<ParserPosition>>) =
        // NOTE : The calculation below relies on the specific behavior of Set.fold, which traverses
        // elements from least to greatest. This allows us to simply add the first position we see for
        // each (nonterminal, productionIndex) pair, instead of having to check if each position is the minimum.
        (Map.empty, freePositions)
        ||> Set.fold (fun recognitionPoints (productionRuleId, parserPosition) ->
            if Map.containsKey productionRuleId recognitionPoints then
                recognitionPoints
            else
                Map.add productionRuleId parserPosition recognitionPoints)


//
[<RequireQualifiedAccess>]
module RecognitionPoints =
    /// <summary>Calculates the recognition points for each production rule in a grammar.</summary>
    /// <remarks>
    /// <para>In "Recursive Ascent-Descent Parsing", Horspool defines a _recognition_point_ of a production rule
    /// as a _free_position_ where all positions to the right of it are also free positions. Note that all production rules
    /// have at least one (1) recognition point; in the worst case, the recognition point is simply the right-most
    /// position in the rule (the right-most position is always a free position).</para>
    /// </remarks>
    let calculate (freePositions : Set<ProductionRuleId * int<ParserPosition>>) =
        (freePositions, Map.empty)
        ||> Set.foldBack (fun (productionRuleId, parserPosition) recognitionPoints ->            
            match Map.tryFind productionRuleId recognitionPoints with
            | None ->
                // There must be at least one recognition point for each rule,
                // so if the map doesn't already contain an entry for this key
                // this position must be the right-most position (always a recognition point).
                Map.add productionRuleId (Set.singleton parserPosition) recognitionPoints
            | Some points ->
                // If this parser position is adjacent to the minimum element of
                // the existing set of recognition points for this production rule,
                // add it to the set and update the map.
                if parserPosition = Set.minElement points - 1<_> then
                    let points = Set.add parserPosition points
                    Map.add productionRuleId points recognitionPoints
                else
                    recognitionPoints)

    /// Determines the earliest (leftmost) recognition point for each production rule,
    /// given a Map containing the set of recognition points for each rule.
    let inline earliest (recognitionPoints : Map<ProductionRuleId, Set<int<ParserPosition>>>) =
        recognitionPoints
        |> Map.map (fun _ ->
            Set.minElement)

