(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpLex.Graph

open System.Diagnostics
open LanguagePrimitives
open SpecializedCollections


/// DFA state.
[<Measure>] type DfaState
/// Unique identifier for a state within a DFA.
type DfaStateId = int<DfaState>

/// <summary>The source and target state of a transition
/// edge in an NFA transition graph.</summary>
/// <remarks>Used as a key for sparse graph implementations
/// because it's more efficient than an F# tuple.</remarks>
[<Struct>]
[<DebuggerDisplay("{Source} -> {Target}")>]
type TransitionEdgeKey =
    /// The source vertex of the edge.
    val Source : DfaStateId
    /// The target vertex of the edge.
    val Target : DfaStateId

    new (source, target) =
        {   Source = source;
            Target = target; }

/// <summary>An immutable implementation of a vertex- and edge-labeled sparse multidigraph,
/// modified for better performance when creating DFAs for lexers.</summary>
/// <remarks>Assumes vertex ids are assigned in order (i.e., there are no gaps in the values),
/// starting at zero (0).</remarks>
[<DebuggerDisplay(
    "Vertices = {VertexCount}, \
     EdgeSets = {EdgeSetCount}, \
     Edges = {EdgeCount}")>]
type LexerDfaGraph private (vertexCount : int, adjacencyMap : Map<TransitionEdgeKey, CharSet>, eofTransition : TransitionEdgeKey option) =
    //
    static let empty =
        LexerDfaGraph (GenericZero, Map.empty, None)

    //
    static member internal Empty
        with get () = empty

    //
    member __.IsEmpty
        with get () =
            vertexCount = GenericZero

    //
    member __.AdjacencyMap
        with get () = adjacencyMap
    
    //
    member __.EofTransition
        with get () = eofTransition

    //
    member __.VertexCount
        with get () = vertexCount

    //
    member internal __.EdgeSetCount
        with get () = adjacencyMap.Count

    //
    member internal __.EdgeCount
        with get () =
            let seed = if Option.isSome eofTransition then 1 else 0
            (seed, adjacencyMap)
            ||> Map.fold (fun edgeCount _ edgeSet ->
                edgeCount + CharSet.count edgeSet)

    //
    member __.CreateVertex () =
        let newVertex : DfaStateId = Int32WithMeasure vertexCount
        newVertex,
        LexerDfaGraph (
            vertexCount + 1,
            adjacencyMap,
            eofTransition)

    //
    member __.TryGetEdgeSet (source : DfaStateId, target : DfaStateId) =
        // Preconditions
        if int source < 0 || int source >= vertexCount then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif int target < 0 || int target >= vertexCount then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        let key = TransitionEdgeKey (source, target)
        Map.tryFind key adjacencyMap

    //
    member __.AddEdges (source : DfaStateId, target : DfaStateId, edges : CharSet) =
        // Preconditions
        if int source < 0 || int source >= vertexCount then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif int target < 0 || int target >= vertexCount then
            invalidArg "target" "The vertex is not in the graph's vertex-set."
        elif CharSet.isEmpty edges then
            invalidArg "edges" "The set of edges to be added is empty."

        let key = TransitionEdgeKey (source, target)

        //
        let edgeSet =
            match Map.tryFind key adjacencyMap with
            | Some edgeSet ->
                CharSet.union edgeSet edges
            | None ->
                edges

        LexerDfaGraph (
            vertexCount,
            Map.add key edgeSet adjacencyMap,
            eofTransition)

    //
    member __.AddEofEdge (source : DfaStateId, target : DfaStateId) =
        // Preconditions
        if int source < 0 || int source >= vertexCount then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif int target < 0 || int target >= vertexCount then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        let eofEdgeKey = TransitionEdgeKey (source, target)

        LexerDfaGraph (
            vertexCount,
            adjacencyMap,
            Some eofEdgeKey)
        
/// Functions on LexerDfaGraph.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LexerDfaGraph =
    /// The empty graph.
    let empty = LexerDfaGraph.Empty

    /// Determines if the graph is empty -- i.e., if it's vertex set is empty.
    let inline isEmpty (graph : LexerDfaGraph) =
        graph.IsEmpty

    //
    let inline createVertex (graph : LexerDfaGraph) =
        graph.CreateVertex ()

    //
    let inline addEdges source target edges (graph : LexerDfaGraph) =
        graph.AddEdges (source, target, edges)

    //
    let inline tryGetEdgeSet source target (graph : LexerDfaGraph) =
        graph.TryGetEdgeSet (source, target)

    //
    let inline addEofEdge source target (graph : LexerDfaGraph) =
        graph.AddEofEdge (source, target)

