(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace FSharpYacc.Graph

open System.Diagnostics


/// An immutable implementation of a vertex-labeled sparse digraph.
[<DebuggerDisplay(
    "Vertices = {VertexCount}, \
     Edges = {EdgeCount}")>]
type internal VertexLabeledSparseDigraph<[<EqualityConditionalOn>]'Vertex when 'Vertex : comparison>
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
    member private __.VertexCount
        with get () =
            Set.count vertices

    //
    member private __.EdgeCount
        with get () =
            Set.count edges

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

    //
    member __.Reverse () =
        /// The set of reversed edges.
        let reversedEdges =
            edges
            |> Set.map (fun (source, target) ->
                target, source)

        VertexLabeledSparseDigraph (
            vertices,
            reversedEdges)


/// Functions on VertexLabeledSparseDigraphs.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal VertexLabeledSparseDigraph =
    /// The empty graph.
    [<GeneralizableValue>]
    let empty<'Vertex when 'Vertex : comparison> =
        VertexLabeledSparseDigraph<'Vertex>.Empty

    /// Determines if the graph is empty -- i.e., if it's vertex set is empty.
    let inline isEmpty (graph : VertexLabeledSparseDigraph<'Vertex>) =
        graph.IsEmpty

    (* TODO :   Implement a function to determine if the graph's edge-set is empty;
                i.e., it may (or may not) have some vertices, but it does not have any edges. *)

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

    /// Creates a VertexLabeledSparseDigraph from a list of edges.
    let ofEdgeList (edgeList : ('Vertex * 'Vertex) list) =
        (VertexLabeledSparseDigraph.Empty, edgeList)
        ||> List.fold (fun graph (source, target) ->
            graph
            |> addVertex source
            |> addVertex target
            |> addEdge source target)            

    //
    let predecessors (graph : VertexLabeledSparseDigraph<'Vertex>) =
        let initialMap =
            (Map.empty, graph.Vertices)
            ||> Set.fold (fun initialMap vertex ->
                Map.add vertex Set.empty initialMap)

        (initialMap, graph.Edges)
        ||> Set.fold (fun predecessorsOf (source, target) ->
            let predsOfTarget =
                Map.find target predecessorsOf
                // Add the source vertex to the predecessor set of target.
                |> Set.add source

            // Add the updated set to the map.
            Map.add target predsOfTarget predecessorsOf)

    //
    let successors (graph : VertexLabeledSparseDigraph<'Vertex>) =
        let initialMap =
            (Map.empty, graph.Vertices)
            ||> Set.fold (fun initialMap vertex ->
                Map.add vertex Set.empty initialMap)

        (initialMap, graph.Edges)
        ||> Set.fold (fun successorsOf (source, target) ->
            let successorsOfSource =
                Map.find source successorsOf
                // Add the target vertex to the successor set of source.
                |> Set.add target

            // Add the updated set to the map.
            Map.add source successorsOfSource successorsOf)

    //
    let dominators (graph : VertexLabeledSparseDigraph<'Vertex>) =
        // If the graph's vertex-set is empty, return an
        // empty map instead of raising an exception.
        if isEmpty graph then
            Choice1Of2 Map.empty
        else
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
                Choice2Of2 "The graph's vertex set is empty; or the graph is not a DAG."
            | 1 ->
                Choice1Of2 <| Set.minElement roots
            | n ->
                Choice2Of2 "The graph contains multiple components (i.e., the graph is not connected)."

        // TODO : Clean this up using the Either workflow.
        match root with
        | Choice2Of2 errorMsg ->
            Choice2Of2 errorMsg
        | Choice1Of2 root ->
            /// The predecessors of each vertex.
            let predecessorsOf = predecessors graph

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
            |> Choice1Of2

    /// Computes the set of vertices reachable from each vertex in a graph.
    // NOTE : This is equivalent to computing the non-reflexive transitive closure of the graph.
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

    (* TODO :   Copy the 'reachable' function, then modify it slightly
                so it computes the _reflexive_ transitive closure. *)

    /// Computes the strongly-connected components of a graph using
    /// Tarjan's offline strongly-connected components algorithm.
    let stronglyConnectedComponents (graph : VertexLabeledSparseDigraph<'Vertex>) =
        // If the graph's vertex-set is empty, return immediately.
        if isEmpty graph then
            Set.empty
        else
            /// The successor sets of the graph vertices.
            let successorsOf = successors graph

            //
            let rec scc (sccs : Set<Set<'Vertex>>,
                                            indices : Map<'Vertex, int>,
                                            lowlink : Map<'Vertex, int>,
                                            stack : 'Vertex list) (vertex : 'Vertex) =
                let index = indices.Count
                let indices = Map.add vertex index indices
                let lowlink = Map.add vertex index lowlink
                let stack = vertex :: stack

                // Examine the successors of the current vertex.
                let successors = Map.find vertex successorsOf
                let sccs, indices, lowlink, stack =
                    ((sccs, indices, lowlink, stack), successors)
                    ||> Set.fold (fun ((sccs, indices, lowlink, stack) as state) successor ->
                        if not <| Map.containsKey successor indices then
                            // The successor has not been visited yet; do so now.
                            let sccs, indices, lowlink, stack =
                                scc state successor
                            let lowlink = Map.add vertex (min (Map.find vertex lowlink) (Map.find successor lowlink)) lowlink
                            sccs, indices, lowlink, stack
                        elif List.exists ((=) successor) stack then
                            // The successor is in the same SCC as the current vertex.
                            let lowlink = Map.add vertex (min (Map.find vertex lowlink) (Map.find successor indices)) lowlink
                            sccs, indices, lowlink, stack
                        else state)

                // If v is a root node, pop the stack and generate an SCC
                if Map.find vertex lowlink = Map.find vertex indices then
                    let mutable scc = Set.empty
                    let mutable stack = stack

                    while List.head stack <> vertex do
                        scc <- Set.add (List.head stack) scc
                        stack <- List.tail stack

                    // The head of the stack should be this vertex itself.
                    // Remove it from the stack and add it to the SCC.
                    assert (List.head stack = vertex)
                    scc <- Set.add (List.head stack) scc
                    stack <- List.tail stack

                    // Add the new SCC to the set of SCCs and continue processing.
                    (Set.add scc sccs), indices, lowlink, stack
                else
                    sccs, indices, lowlink, stack

            // TODO : Modify this function to use CPS or re-implement
            // the algorithm so it's tail-recursive.
            ((Set.empty, Map.empty, Map.empty, List.empty), graph.Vertices)
            ||> Set.fold (fun ((_, indices, _, _) as state) vertex ->
                if Map.containsKey vertex indices then
                    state
                else
                    scc state vertex)
            // Return the set of strongly-connected components.
            |> fun (sccs,_,_,_) -> sccs

    /// Compute the 'condensation' of a graph by condensing each of
    /// it's strongly-connected components into a single vertex.
    let condense (graph : VertexLabeledSparseDigraph<'Vertex>) : VertexLabeledSparseDigraph<Set<'Vertex>> =
        //
        raise <| System.NotImplementedException "VertexLabeledSparseDigraph.condense"


/// An immutable implementation of a vertex- and edge-labeled sparse digraph.
[<DebuggerDisplay(
    "Vertices = {VertexCount}, \
     Edges = {EdgeCount}")>]
type LabeledSparseDigraph<[<EqualityConditionalOn>]'Vertex, [<EqualityConditionalOn; ComparisonConditionalOn>]'Edge when 'Vertex : comparison>
        private (vertices : Set<'Vertex>, edges : Map<'Vertex * 'Vertex, 'Edge>) =
    //
    static member internal Empty
        with get () = LabeledSparseDigraph<'Vertex, 'Edge> (Set.empty, Map.empty)

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
    member private __.VertexCount
        with get () =
            Set.count vertices

    //
    member private __.EdgeCount
        with get () =
            edges.Count

    //
    static member Create (vertices : Set<'Vertex>) =
        LabeledSparseDigraph (
            vertices,
            Map.empty)

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

        Map.containsKey (source, target) edges

    //
    member __.GetEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertices then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertices then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        Map.find (source, target) edges

    //
    member __.TryGetEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertices then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertices then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        Map.tryFind (source, target) edges

    //
    member __.AddVertex (vertex : 'Vertex) =
        LabeledSparseDigraph (
            Set.add vertex vertices,
            edges)

    //
    member __.AddVertices (vertices : Set<'Vertex>) =
        LabeledSparseDigraph (
            Set.union vertices vertices,
            edges)

    //
    member __.AddEdge (source : 'Vertex, target : 'Vertex, edge : 'Edge) =
        // Preconditions
        if not <| Set.contains source vertices then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertices then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        LabeledSparseDigraph (
            vertices,
            Map.add (source, target) edge edges)

    //
    member __.RemoveVertex (vertex : 'Vertex) =
        // Preconditions
        if not <| Set.contains vertex vertices then
            invalidArg "vertex" "The vertex is not in the graph's vertex-set."

        // Remove in- and out-edgeSet of the vertex.
        let edges =
            edges
            |> Map.filter (fun (source, target) _ ->
                source <> vertex
                && target <> vertex)

        LabeledSparseDigraph (
            Set.remove vertex vertices,
            edges)

    //
    member __.RemoveEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertices then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertices then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        LabeledSparseDigraph (
            vertices,
            Map.remove (source, target) edges)
    

/// Functions on LabeledSparseDigraphs.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LabeledSparseDigraph =
    /// The empty graph.
    [<GeneralizableValue>]
    let empty<'Vertex, 'Edge when 'Vertex : comparison> =
        LabeledSparseDigraph<'Vertex,'Edge>.Empty

    /// Determines if the graph is empty -- i.e., if it's vertex set is empty.
    let inline isEmpty (graph : LabeledSparseDigraph<'Vertex, 'Edge>) =
        graph.IsEmpty

    /// Creates a graph from a set of vertices.
    let inline ofVertexSet (vertices : Set<'Vertex>) : LabeledSparseDigraph<'Vertex, 'Edge> =
        LabeledSparseDigraph<'Vertex, 'Edge>.Create vertices

    //
    let inline addVertex (vertex : 'Vertex) (graph : LabeledSparseDigraph<'Vertex, 'Edge>) =
        graph.AddVertex vertex

    //
    let inline addVertices (vertices : Set<'Vertex>) (graph : LabeledSparseDigraph<'Vertex, 'Edge>) =
        graph.AddVertices vertices

    //
    let inline addEdge source target edge (graph : LabeledSparseDigraph<'Vertex, 'Edge>) =
        graph.AddEdge (source, target, edge)

    //
    let inline removeVertex (vertex : 'Vertex) (graph : LabeledSparseDigraph<'Vertex, 'Edge>) =
        graph.RemoveVertex vertex

    //
    let inline removeEdge source target (graph : LabeledSparseDigraph<'Vertex, 'Edge>) =
        graph.RemoveEdge (source, target)

    //
    let inline containsVertex (vertex : 'Vertex) (graph : LabeledSparseDigraph<'Vertex, 'Edge>) =
        graph.ContainsVertex vertex

    //
    let inline containsEdge source target (graph : LabeledSparseDigraph<'Vertex, 'Edge>) =
        graph.ContainsEdge (source, target)

    //
    let inline getEdge source target (graph : LabeledSparseDigraph<'Vertex, 'Edge>) =
        graph.GetEdge (source, target)

    //
    let inline tryGetEdge source target (graph : LabeledSparseDigraph<'Vertex, 'Edge>) =
        graph.TryGetEdge (source, target)


