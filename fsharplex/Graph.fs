(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpLex.Graph


/// An immutable implementation of a vertex- and edge-labeled sparse digraph.
type LabeledSparseDigraph<[<EqualityConditionalOn>]'Vertex, [<EqualityConditionalOn; ComparisonConditionalOn>]'Edge when 'Vertex : comparison>
        private (vertexSet : Set<'Vertex>, edgeSet : Map<'Vertex * 'Vertex, 'Edge>) =
    //
    static member internal Empty
        with get () = LabeledSparseDigraph<'Vertex, 'Edge> (Set.empty, Map.empty)

    //
    member __.IsEmpty
        with get () = Set.isEmpty vertexSet

    //
    member __.Edges
        with get () = edgeSet
    
    //
    member __.Vertices
        with get () = vertexSet

    //
    static member Create (vertices : Set<'Vertex>) =
        LabeledSparseDigraph (
            vertices,
            Map.empty)

    //
    member __.ContainsVertex (vertex : 'Vertex) =
        Set.contains vertex vertexSet

    //
    member __.ContainsEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertexSet then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertexSet then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        Map.containsKey (source, target) edgeSet

    //
    member __.GetEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertexSet then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertexSet then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        Map.find (source, target) edgeSet

    //
    member __.TryGetEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertexSet then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertexSet then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        Map.tryFind (source, target) edgeSet

    //
    member __.AddVertex (vertex : 'Vertex) =
        LabeledSparseDigraph (
            Set.add vertex vertexSet,
            edgeSet)

    //
    member __.AddVertices (vertices : Set<'Vertex>) =
        LabeledSparseDigraph (
            Set.union vertexSet vertices,
            edgeSet)

    //
    member __.AddEdge (source : 'Vertex, target : 'Vertex, edge : 'Edge) =
        // Preconditions
        if not <| Set.contains source vertexSet then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertexSet then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        LabeledSparseDigraph (
            vertexSet,
            Map.add (source, target) edge edgeSet)

    //
    member __.RemoveVertex (vertex : 'Vertex) =
        // Preconditions
        if not <| Set.contains vertex vertexSet then
            invalidArg "vertex" "The vertex is not in the graph's vertex-set."

        // Remove in- and out-edgeSet of the vertex.
        let edgeSet =
            edgeSet
            |> Map.filter (fun (source, target) _ ->
                source <> vertex
                && target <> vertex)

        LabeledSparseDigraph (
            Set.remove vertex vertexSet,
            edgeSet)

    //
    member __.RemoveEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertexSet then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertexSet then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        LabeledSparseDigraph (
            vertexSet,
            Map.remove (source, target) edgeSet)
    

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


//
/// An immutable implementation of a vertex- and edge-labeled sparse multidigraph.
type LabeledSparseMultidigraph<[<EqualityConditionalOn>]'Vertex, [<EqualityConditionalOn>]'Edge when 'Vertex : comparison and 'Edge : comparison>
        private (vertexSet : Set<'Vertex>, edgeSets : Map<'Vertex * 'Vertex, Set<'Edge>>) =
    //
    static member internal Empty
        with get () = LabeledSparseMultidigraph<'Vertex, 'Edge> (Set.empty, Map.empty)

    //
    member __.IsEmpty
        with get () = Set.isEmpty vertexSet

    //
    member __.EdgeSets
        with get () = edgeSets
    
    //
    member __.Vertices
        with get () = vertexSet

    //
    static member Create (vertices : Set<'Vertex>) =
        LabeledSparseMultidigraph (
            vertices,
            Map.empty)

    //
    member __.ContainsVertex (vertex : 'Vertex) =
        Set.contains vertex vertexSet

    //
    member __.ContainsEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertexSet then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertexSet then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        Map.containsKey (source, target) edgeSets

    //
    member __.GetEdgeSet (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertexSet then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertexSet then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        Map.find (source, target) edgeSets

    //
    member __.TryGetEdgeSet (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertexSet then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertexSet then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        Map.tryFind (source, target) edgeSets

    //
    member __.AddVertex (vertex : 'Vertex) =
        LabeledSparseMultidigraph (
            Set.add vertex vertexSet,
            edgeSets)

    //
    member __.AddVertices (vertices : Set<'Vertex>) =
        LabeledSparseMultidigraph (
            Set.union vertexSet vertices,
            edgeSets)

    //
    member __.AddEdge (source : 'Vertex, target : 'Vertex, edge : 'Edge) =
        // Preconditions
        if not <| Set.contains source vertexSet then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertexSet then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        //
        let edgeSet =
            match Map.tryFind (source, target) edgeSets with
            | Some edgeSet ->
                Set.add edge edgeSet
            | None ->
                Set.singleton edge        

        LabeledSparseMultidigraph (
            vertexSet,
            Map.add (source, target) edgeSet edgeSets)

    //
    member __.RemoveVertex (vertex : 'Vertex) =
        // Preconditions
        if not <| Set.contains vertex vertexSet then
            invalidArg "vertex" "The vertex is not in the graph's vertex-set."

        // Remove in- and out-edges of the vertex.
        let edgeSets =
            edgeSets
            |> Map.filter (fun (source, target) _ ->
                source <> vertex
                && target <> vertex)

        LabeledSparseMultidigraph (
            Set.remove vertex vertexSet,
            edgeSets)

    //
    member __.RemoveAllEdges (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertexSet then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertexSet then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        LabeledSparseMultidigraph (
            vertexSet,
            Map.remove (source, target) edgeSets)

    //
    member this.RemoveEdge (source : 'Vertex, target : 'Vertex, edge : 'Edge) =
        // Preconditions
        if not <| Set.contains source vertexSet then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertexSet then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        // Try to retrieve the edge-set for these vertexSet.
        match Map.tryFind (source, target) edgeSets with
        | None ->
            // Nothing to do, so just return the original graph.
            this
        | Some edgeSet ->
            // Remove the edge from the edge-set.
            let edgeSet = Set.remove edge edgeSet

            // If the edge-set is empty after removing the edge, remove it from 'edges';
            // otherwise, update 'edges' with the modified edge-set.
            let edgeSets =
                if Set.isEmpty edgeSet then
                    Map.remove (source, target) edgeSets
                else
                    Map.add (source, target) edgeSet edgeSets

            LabeledSparseMultidigraph (
                vertexSet, edgeSets)
        
/// Functions on LabeledSparseMultidigraph.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LabeledSparseMultidigraph =
    /// The empty graph.
    [<GeneralizableValue>]
    let empty<'Vertex, 'Edge when 'Vertex : comparison and 'Edge : comparison> =
        LabeledSparseMultidigraph<'Vertex,'Edge>.Empty

    /// Determines if the graph is empty -- i.e., if it's vertex set is empty.
    let inline isEmpty (graph : LabeledSparseMultidigraph<'Vertex, 'Edge>) =
        graph.IsEmpty

    /// Creates a graph from a set of vertices.
    let inline ofVertexSet (vertices : Set<'Vertex>) : LabeledSparseMultidigraph<'Vertex, 'Edge> =
        LabeledSparseMultidigraph<'Vertex, 'Edge>.Create vertices

    //
    let inline addVertex (vertex : 'Vertex) (graph : LabeledSparseMultidigraph<'Vertex, 'Edge>) =
        graph.AddVertex vertex

    //
    let inline addVertices (vertices : Set<'Vertex>) (graph : LabeledSparseMultidigraph<'Vertex, 'Edge>) =
        graph.AddVertices vertices

    //
    let inline addEdge source target edge (graph : LabeledSparseMultidigraph<'Vertex, 'Edge>) =
        graph.AddEdge (source, target, edge)

    //
    let inline removeVertex (vertex : 'Vertex) (graph : LabeledSparseMultidigraph<'Vertex, 'Edge>) =
        graph.RemoveVertex vertex

    //
    let inline removeAllEdges source target (graph : LabeledSparseMultidigraph<'Vertex, 'Edge>) =
        graph.RemoveAllEdges (source, target)

    //
    let inline removeEdge source target edge (graph : LabeledSparseMultidigraph<'Vertex, 'Edge>) =
        graph.RemoveEdge (source, target, edge)

    //
    let inline containsVertex (vertex : 'Vertex) (graph : LabeledSparseMultidigraph<'Vertex, 'Edge>) =
        graph.ContainsVertex vertex

    //
    let inline containsEdge source target (graph : LabeledSparseMultidigraph<'Vertex, 'Edge>) =
        graph.ContainsEdge (source, target)

    //
    let inline getEdgeSet source target (graph : LabeledSparseMultidigraph<'Vertex, 'Edge>) =
        graph.GetEdgeSet (source, target)

    //
    let inline tryGetEdgeSet source target (graph : LabeledSparseMultidigraph<'Vertex, 'Edge>) =
        graph.TryGetEdgeSet (source, target)
