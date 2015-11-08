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

namespace Reggie.Graph

open System.Diagnostics
open LanguagePrimitives
open Reggie.SpecializedCollections


/// DFA state.
[<Measure>] type DfaState

/// Unique identifier for a state within a DFA.
type DfaStateId = int<DfaState>

/// <summary>An immutable implementation of a vertex- and edge-labeled sparse multidigraph representing a DFA.</summary>
/// <remarks>Assumes vertex ids are assigned in order (i.e., there are no gaps in the values), starting at zero (0).</remarks>
[<Struct>]
[<DebuggerDisplay("Vertices = {VertexCount}, EdgeSets = {EdgeSetCount}, Edges = {EdgeCount}")>]
type LexerDfaGraph =
    //
    val private InternalAdjacencyMap : TagMap<DfaState, TagMap<DfaState, CharSet>> option;
    //
    // Source-Vertex * Target-Vertex
    val EofTransitionEdge : (DfaStateId * DfaStateId) option;
    //
    val VertexCount : int32;

    //
    new (internalAdjacencyMap, eofTransitionEdge, vertexCount) =
        { InternalAdjacencyMap = internalAdjacencyMap;
          EofTransitionEdge = eofTransitionEdge;
          VertexCount = vertexCount; }

    /// An empty DfaGraph.
    static member Empty
        with get () =
            Unchecked.defaultof<LexerDfaGraph>

    //
    member this.IsEmpty
        with get () =
            this.VertexCount = GenericZero

    /// Returns the adjancency map for the graph.
    /// The keys of the outer map are 'source' DFA states -- states with one or more out-transitions from the state.
    /// The keys of the inner map are the DFA states targeted by transitions from the corresponding key from the outer map.
    /// The values of the inner map are CharSets representing the set of characters labeling the transitions from the
    /// corresponding 'source' state to the corresponding 'target state.
    member this.AdjacencyMap
        with get () =
            defaultArg this.InternalAdjacencyMap TagMap.empty

    //
    member private this.EdgeSetCount
        with get () =
            let seed = if Option.isNone this.EofTransitionEdge then 0 else 1
            (seed, this.AdjacencyMap)
            ||> TagMap.fold (fun count _ innerMap ->
                count + TagMap.count innerMap)

    //
    member private this.EdgeCount
        with get () =
            let seed = if Option.isNone this.EofTransitionEdge then 0 else 1
            (seed, this.AdjacencyMap)
            ||> TagMap.fold (fun count _ innerMap ->
                (count, innerMap)
                ||> TagMap.fold (fun count _ edgeChars ->
                    count + CharSet.count edgeChars))

    //
    member this.CreateVertex () =
        let vertexCount = this.VertexCount
        let newVertex : int<'Tag> = tag vertexCount
        newVertex,
        LexerDfaGraph (
            this.InternalAdjacencyMap,
            this.EofTransitionEdge,
            vertexCount + 1)

    //
    member this.TryGetEdgeSet (source : DfaStateId) (target : DfaStateId) =
        // Preconditions
        if int source < 0 || int source >= this.VertexCount then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif int target < 0 || int target >= this.VertexCount then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        this.InternalAdjacencyMap
        |> Option.bind (fun adjMap ->
            TagMap.tryFind source adjMap)
        |> Option.bind (fun targetMap ->
            TagMap.tryFind target targetMap)

    //
    member this.AddEdges (source : DfaStateId) (target : DfaStateId) (edges : CharSet) =
        // Preconditions
        if int source < 0 || int source >= this.VertexCount then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif int target < 0 || int target >= this.VertexCount then
            invalidArg "target" "The vertex is not in the graph's vertex-set."
        elif CharSet.isEmpty edges then
            invalidArg "edges" "The set of edges to be added is empty."

        let newAdjMap =
            match this.InternalAdjacencyMap with
            | None ->
                edges
                |> TagMap.singleton target
                |> TagMap.singleton source

            | Some adjMap ->
                match TagMap.tryFind source adjMap with
                | None ->
                    TagMap.add source (TagMap.singleton target edges) adjMap

                | Some targetMap ->
                    match TagMap.tryFind target targetMap with
                    | None ->
                        TagMap.add source (TagMap.add target edges targetMap) adjMap

                    | Some existingEdges ->
                        TagMap.add source (TagMap.add target (CharSet.union existingEdges edges) targetMap) adjMap

        LexerDfaGraph (Some newAdjMap, this.EofTransitionEdge, this.VertexCount)

    //
    member this.AddEofEdge (source : DfaStateId) (target : DfaStateId) =
        // Preconditions
        if int source < 0 || int source >= this.VertexCount then
            invalidArg "source" "The vertex is not in the graph's vertex-set."
        elif int target < 0 || int target >= this.VertexCount then
            invalidArg "target" "The vertex is not in the graph's vertex-set."

        LexerDfaGraph (
            this.InternalAdjacencyMap,
            Some (source, target),
            this.VertexCount)
