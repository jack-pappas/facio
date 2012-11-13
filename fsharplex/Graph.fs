(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpLex.Graph


/// An immutable implementation of a directed,
/// labeled-edge sparse graph.
type SparseGraph<[<EqualityConditionalOn>]'Vertex, [<EqualityConditionalOn; ComparisonConditionalOn>]'Edge when 'Vertex : comparison>
                private (vertices : Set<'Vertex>, edges : Map<'Vertex * 'Vertex, 'Edge>) =
    //
    static member internal Empty
        with get () = SparseGraph<'Vertex, 'Edge> (Set.empty, Map.empty)

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
        SparseGraph (
            Set.add vertex vertices,
            edges)

    //
    member __.AddEdge (source : 'Vertex, target : 'Vertex, edge : 'Edge) =
        // Preconditions
        if not <| Set.contains source vertices then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertices then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        SparseGraph (
            vertices,
            Map.add (source, target) edge edges)

    //
    member __.RemoveVertex (vertex : 'Vertex) =
        // Preconditions
        if not <| Set.contains vertex vertices then
            invalidArg "vertex" "The vertex is not in the graph's vertex-set."

        // Remove in- and out-edges of the vertex.
        let edges =
            edges
            |> Map.filter (fun (source, target) _ ->
                source <> vertex
                && target <> vertex)

        SparseGraph (
            Set.remove vertex vertices,
            edges)

    //
    member __.RemoveEdge (source : 'Vertex, target : 'Vertex) =
        // Preconditions
        if not <| Set.contains source vertices then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif not <| Set.contains target vertices then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        SparseGraph (
            vertices,
            Map.remove (source, target) edges)
    

/// Functions on immutable sparse graphs.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module SparseGraph =
    /// The empty graph.
    [<GeneralizableValue>]
    let empty<'Vertex, 'Edge when 'Vertex : comparison> =
        SparseGraph<'Vertex,'Edge>.Empty

    /// Determines if the graph is empty -- i.e., if it's vertex set is empty.
    let inline isEmpty (graph : SparseGraph<'Vertex, 'Edge>) =
        graph.IsEmpty

    //
    let inline addVertex (vertex : 'Vertex) (graph : SparseGraph<'Vertex, 'Edge>) =
        graph.AddVertex vertex

    //
    let inline addEdge source target edge (graph : SparseGraph<'Vertex, 'Edge>) =
        graph.AddEdge (source, target, edge)

    //
    let inline removeVertex (vertex : 'Vertex) (graph : SparseGraph<'Vertex, 'Edge>) =
        graph.RemoveVertex vertex

    //
    let inline removeEdge source target (graph : SparseGraph<'Vertex, 'Edge>) =
        graph.RemoveEdge (source, target)

    //
    let inline containsVertex (vertex : 'Vertex) (graph : SparseGraph<'Vertex, 'Edge>) =
        graph.ContainsVertex vertex

    //
    let inline containsEdge source target (graph : SparseGraph<'Vertex, 'Edge>) =
        graph.ContainsEdge (source, target)

    //
    let inline getEdge source target (graph : SparseGraph<'Vertex, 'Edge>) =
        graph.GetEdge (source, target)

    //
    let inline tryGetEdge source target (graph : SparseGraph<'Vertex, 'Edge>) =
        graph.TryGetEdge (source, target)



