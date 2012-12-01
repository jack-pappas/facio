(*
Copyright (c) 2012, Jack Pappas
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
type LexerDfaGraph private (vertexCount : int, adjacencyMap : Map<TransitionEdgeKey, CharSet>) =
    //
    static let empty =
        LexerDfaGraph (GenericZero, Map.empty)

    //
    static member internal Empty
        with get () = empty

    //
    member __.IsEmpty
        with get () =
            vertexCount = GenericZero

    //
    member __.EdgeSets
        with get () = adjacencyMap
    
    //
    member __.VertexCount
        with get () = vertexCount

    //
    member __.CreateVertex () =
        let newVertex = Int32WithMeasure<'Vertex> <| vertexCount + 1
        newVertex,
        LexerDfaGraph (
            vertexCount + 1,
            adjacencyMap)

    //
    member __.TryGetEdgeSet (source : DfaStateId, target : DfaStateId) =
        // Preconditions
        if int source <= 0 || int source > vertexCount then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif int target <= 0 || int target > vertexCount then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        let key = TransitionEdgeKey (source, target)
        Map.tryFind key adjacencyMap

    //
    member __.AddEdge (source : DfaStateId, target : DfaStateId, edge : CharSet) =
        // Preconditions
        if int source <= 0 || int source > vertexCount then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif int target <= 0 || int target > vertexCount then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        let key = TransitionEdgeKey (source, target)

//        //
//        let edgeSet =
//            match Map.tryFind key adjacencyMap with
//            | Some edgeSet ->
//                CharSet.add edge edgeSet
//            | None ->
//                CharSet.singleton edge

        LexerDfaGraph (
            vertexCount,
            Map.add key edge adjacencyMap)
            //Map.add key edgeSet adjacencyMap)

        
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
    let inline addEdge source target edge (graph : LexerDfaGraph) =
        graph.AddEdge (source, target, edge)

    //
    let inline tryGetEdgeSet source target (graph : LexerDfaGraph) =
        graph.TryGetEdgeSet (source, target)

