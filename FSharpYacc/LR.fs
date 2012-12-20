(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

/// Parser table generators for LR(k) grammars.
namespace FSharpYacc.LR

open LanguagePrimitives
open FSharpYacc.Grammar
open AugmentedPatterns
open FSharpYacc.Analysis


/// An LR(k) item.
type internal LrItem<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    Nonterminal : 'Nonterminal;
    //
    Production : Symbol<'Nonterminal, 'Terminal>[];
    //
    Position : int<ParserPosition>;
    //
    Lookahead : 'Lookahead;
} with
    /// <inherit />
    override this.ToString () =
        let sb = System.Text.StringBuilder ()

        // Add the nonterminal text and arrow to the StringBuilder.
        sprintf "%O \u2192 " this.Nonterminal
        |> sb.Append |> ignore

        for i = 0 to Array.length this.Production do
            if i < int this.Position then
                this.Production.[i].ToString ()
                |> sb.Append |> ignore
            elif i = int this.Position then
                // Append the dot character representing the parser position.
                sb.Append "\u2022" |> ignore
            else
                this.Production.[i - 1].ToString ()
                |> sb.Append |> ignore

        // Append the lookahead symbol, if applicable.
        if typeof<'Lookahead> <> typeof<unit> then
            sprintf ", %A" this.Lookahead
            |> sb.Append |> ignore

        sb.ToString ()

/// An LR(k) parser state -- i.e., a set of LR(k) items.
type internal LrParserState<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> =
    Set<LrItem<'Nonterminal, 'Terminal, 'Lookahead>>

/// An action which manipulates the state of the
/// parser automaton for an LR(k) parser.
type LrParserAction =
    /// Shift into a state.
    | Shift of ParserStateId
    /// Reduce by a production rule.
    | Reduce of ReductionRuleId
    /// Accept.
    | Accept

    /// <inherit />
    override this.ToString () =
        match this with
        | Shift stateId ->
            "s" + stateId.ToString ()
        | Reduce ruleId ->
            "r" + ruleId.ToString ()
        | Accept ->
            "a"

/// LR(k) parser table.
type LrParsingTable<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    ActionTable : Map<ParserStateId * 'Terminal, Set<LrParserAction>>;
    //
    GotoTable : Map<ParserStateId * 'Nonterminal, ParserStateId>;
    //
    ParserStates : Map<ParserStateId, LrParserState<'Nonterminal, 'Terminal, 'Lookahead>>;
    //
    ReductionRulesById : Map<ReductionRuleId, 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]>;
}

/// LR(k) parser table generation state.
type internal LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    ActionTable : Map<ParserStateId * 'Terminal, Set<LrParserAction>>;
    //
    GotoTable : Map<ParserStateId * 'Nonterminal, ParserStateId>;
    //
    ParserStates : Map<LrParserState<'Nonterminal, 'Terminal, 'Lookahead>, ParserStateId>;
    //
    ReductionRules : Map<'Nonterminal * Symbol<'Nonterminal, 'Terminal>[], ReductionRuleId>;
    //
    ReductionRulesById : Map<ReductionRuleId, 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]>;
}

/// Functions which use the State monad to manipulate an LR(k) table-generation state.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal LrTableGenState =
    /// Returns an empty Lr0TableGenState with the given
    /// nonterminal and terminal types.
    let empty : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> = {
        ActionTable = Map.empty;
        GotoTable = Map.empty;
        ParserStates = Map.empty;
        ReductionRules = Map.empty;
        ReductionRulesById = Map.empty; }

    /// Retrives the identifier for a given parser state (set of items).
    /// If the state has not been assigned an identifier, one is created
    /// and added to the table-generation state before returning.
    let stateId
        (parserState : LrParserState<'Nonterminal, 'Terminal, 'Lookahead>)
        (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        // Try to retrieve an existing id for this state.
        match Map.tryFind parserState tableGenState.ParserStates with
        | Some parserStateId ->
            parserStateId, tableGenState

        | None ->
            // Create a new ID for this state.
            let parserStateId =
                tableGenState.ParserStates.Count + 1
                |> Int32WithMeasure

            // Return the id, along with the updated table-gen state.
            parserStateId,
            { tableGenState with
                ParserStates =
                    Map.add parserState parserStateId tableGenState.ParserStates; }

    //
    let reductionRuleId
        (reductionRule : 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[])
        (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        // Reduction rules should only be added, but for safety we'll check to
        // see if the rule has already been assigned an identifier.
        match Map.tryFind reductionRule tableGenState.ReductionRules with
        | Some reductionRuleId ->
            reductionRuleId, tableGenState

        | None ->
            // Create a new ID for this reduction rule.
            let reductionRuleId =
                tableGenState.ReductionRules.Count + 1
                |> Int32WithMeasure

            // Return the id, along with the updated table-gen state.
            reductionRuleId,
            { tableGenState with
                ReductionRules =
                    Map.add reductionRule reductionRuleId tableGenState.ReductionRules;
                ReductionRulesById =
                    Map.add reductionRuleId reductionRule tableGenState.ReductionRulesById; }

    /// Add a 'shift' action to the parser table.
    let shift (sourceState : ParserStateId)
                (transitionSymbol : 'Terminal)
                (targetState : ParserStateId)
                (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        //
        let tableKey = sourceState, transitionSymbol

        //
        let entry =
            let action = LrParserAction.Shift targetState
            match Map.tryFind tableKey tableGenState.ActionTable with
            | None ->
                Set.singleton action
            | Some entry ->
                Set.add action entry

        // Update the table with the new entry.
        (),
        { tableGenState with
            ActionTable = Map.add tableKey entry tableGenState.ActionTable; }

    /// Add a 'goto' action to the parser table.
    let goto (sourceState : ParserStateId)
                (transitionSymbol : 'Nonterminal)
                (targetState : ParserStateId)
                (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        //
        let tableKey = sourceState, transitionSymbol

        //
        match Map.tryFind tableKey tableGenState.GotoTable with
        | None ->
            // Update the table with the new entry.
            (),
            { tableGenState with
                GotoTable = Map.add tableKey targetState tableGenState.GotoTable; }

        | Some entry ->
            // If the existing entry is the same as the target state,
            // there's nothing to do -- just return the existing 'tableGenState'.
            if entry = targetState then
                (), tableGenState
            else
                let msg = sprintf "Cannot add the entry (g%i) to the GOTO table; \
                                    it already contains an entry (g%i) for the key %A."
                                    (int targetState) (int entry) tableKey
                raise <| exn msg        

    /// Add an 'accept' action to the parser table.
    let accept (sourceState : ParserStateId) (tableGenState : LrTableGenState<'Nonterminal, AugmentedTerminal<'Terminal>, 'Lookahead>) =
        //
        let tableKey = sourceState, EndOfFile

        //
        let entry =
            match Map.tryFind tableKey tableGenState.ActionTable with
            | None ->
                // Create a new 'accept' action for this table entry.
                Set.singleton LrParserAction.Accept
            | Some entry ->
                // Create a new 'accept' action and add it to the existing table entry.
                Set.add LrParserAction.Accept entry

        // Update the table with the new entry.
        (),
        { tableGenState with
            ActionTable = Map.add tableKey entry tableGenState.ActionTable; }


/// An LR(0) item.
type internal Lr0Item<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrItem<'Nonterminal, 'Terminal, unit>

/// An LR(0) parser state -- i.e., a set of LR(0) items.
type internal Lr0ParserState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrParserState<'Nonterminal, 'Terminal, unit>

/// LR(0) parser table generation state.
type internal Lr0TableGenState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrTableGenState<'Nonterminal, 'Terminal, unit>

/// LR(0) parser tables.
[<RequireQualifiedAccess>]
module internal Lr0 =
    /// Functions for manipulating LR(0) parser items.
    [<RequireQualifiedAccess>]
    module Item =
        /// Computes the LR(0) closure of a set of items.
        // TODO : Modify this to use a worklist-style algorithm to avoid
        // reprocessing items which already exist in the set (i.e., when iterating,
        // we only process items added to the set in the previous iteration).
        let closure (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) items =
            /// Implementation of the LR(0) closure algorithm.
            let rec closure items =
                let items' =
                    (items, items)
                    ||> Set.fold (fun items item ->
                        // If the position is at the end of the production,
                        // there's nothing that needs to be done for this item.
                        if int item.Position = Array.length item.Production then
                            items
                        else
                            // Determine what to do based on the next symbol to be parsed.
                            match item.Production.[int item.Position] with
                            | Symbol.Terminal _ ->
                                // Nothing to do for terminals
                                items
                            | Symbol.Nonterminal nontermId ->
                                /// The productions of this nonterminal.
                                let nontermProductions = Map.find nontermId productions

                                // For all productions of this nonterminal, create a new item
                                // with the parser position at the beginning of the production.
                                // Add these new items into the set of items.
                                (items, nontermProductions)
                                ||> Array.fold (fun items production ->
                                    let newItem = {
                                        Nonterminal = nontermId;
                                        Production = production;
                                        Position = GenericZero;
                                        Lookahead = (); }

                                    Set.add newItem items))

                // If the items set has changed, recurse for another iteration.
                // If not, we're done processing and the set is returned.
                if items' = items then
                    items
                else
                    closure items'

            // Compute the closure, starting with the specified initial items.
            closure items

        /// Moves the 'dot' (the current parser position) past the
        /// specified symbol for each item in a set of items.
        let goto symbol items (productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>) =
            (Set.empty, items)
            ||> Set.fold (fun updatedItems item ->
                // If the position is at the end of the production, we know
                // this item can't be a match, so continue to to the next item.
                if int item.Position = Array.length item.Production then
                    updatedItems
                else
                    // If the next symbol to be parsed in the production is the
                    // specified symbol, create a new item with the position advanced
                    // to the right of the symbol and add it to the updated items set.
                    if item.Production.[int item.Position] = symbol then
                        let updatedItem =
                            { item with
                                Position = item.Position + 1<_>; }
                        Set.add updatedItem updatedItems
                    else
                        // The symbol did not match, so this item won't be added to
                        // the updated items set.
                        updatedItems)
            // Return the closure of the item set.
            |> closure productions

        /// Determines if an LR(0) item is a 'kernel' item.
        let isKernelItem (item : LrItem<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>, unit>) =
            // An LR(0) item is a kernel item iff it is the initial item or
            // the dot (representing the parser position) is NOT in the leftmost
            // (zeroth) position of the production.
            if item.Position > 0<_> then true
            else
                // Is this the initial item?
                match item.Nonterminal with
                | Start -> true
                | Nonterminal _ -> false


    /// Functions which use the State monad to manipulate an LR(0) table-generation state.
    [<RequireQualifiedAccess>]
    module TableGenState =
        /// Add 'reduce' actions to the parser table for each terminal (token) in the grammar.
        let reduce (sourceState : ParserStateId)
                    (reductionRuleId : ReductionRuleId)
                    (terminals : Set<_>)
                    (tableGenState : Lr0TableGenState<'Nonterminal, AugmentedTerminal<'Terminal>>) =
            // Fold over the set of terminals (tokens) in the grammar.
            let table =
                (tableGenState.ActionTable, terminals)
                ||> Set.fold (fun table token ->
                    //
                    let tableKey = sourceState, token

                    //
                    let entry =
                        let action = LrParserAction.Reduce reductionRuleId
                        match Map.tryFind tableKey table with
                        | None ->
                            Set.singleton action
                        | Some entry ->
                            Set.add action entry

                    // Update the table with the entry.
                    Map.add tableKey entry table)

            // Return the updated table-gen state.
            (),
            { tableGenState with
                ActionTable = table; }


    //
    let rec internal createTableImpl (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) (tableGenState : Lr0TableGenState<_,_>) =
        // Preconditions
        assert (not <| Map.isEmpty tableGenState.ParserStates)

        let tableGenState' =
            (tableGenState, tableGenState.ParserStates)
            ||> Map.fold (fun tableGenState stateItems stateId ->
                (tableGenState, stateItems)
                ||> Set.fold (fun tableGenState item ->
                    // If the parser position is at the end of the production,
                    // add a 'reduce' action for every terminal (token) in the grammar.
                    if int item.Position = Array.length item.Production then
                        // First, add this reduction rule to the table-gen state,
                        // which gives us an identifier for the rule.
                        let reductionRuleId, tableGenState =
                            LrTableGenState.reductionRuleId (item.Nonterminal, item.Production) tableGenState

                        // Add 'reduce' actions to the parser table.
                        TableGenState.reduce stateId reductionRuleId grammar.Terminals tableGenState
                        // TEMP : Discard the unit return value until we can use a monadic fold.
                        |> snd
                    else
                        // Add actions to the table based on the next symbol to be parsed.
                        match item.Production.[int item.Position] with
                        | Symbol.Terminal EndOfFile ->
                            // When the end-of-file symbol is the next to be parsed,
                            // add an 'accept' action to the table to indicate the
                            // input has been parsed successfully.
                            LrTableGenState.accept stateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Terminal (Terminal _ as token) as symbol ->                            
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Item.goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                LrTableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a terminal (token),
                            // so add a 'shift' action to this entry of the table.
                            LrTableGenState.shift stateId token targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Nonterminal nonterm as symbol ->
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Item.goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                LrTableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a nonterminal,
                            // so add a 'goto' action to this entry of the table.
                            LrTableGenState.goto stateId nonterm targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd
                        ))
            
        // If any states or transition-edges have been added, we need to recurse
        // and continue until we reach a fixpoint; otherwise, return the completed table.
        if tableGenState.ParserStates <> tableGenState'.ParserStates ||
            tableGenState.ActionTable <> tableGenState'.ActionTable ||
            tableGenState.GotoTable <> tableGenState'.GotoTable then
            createTableImpl grammar tableGenState'
        else
            tableGenState

    /// Creates an LR(0) parser table from the specified grammar.
    let createTable (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) : LrParsingTable<_,_,_> =
        /// The final table-gen state.
        let finalTableGenState =
            /// The initial state (set of items) passed to 'createTable'.
            let initialParserState =
                grammar.Productions
                |> Map.find Start
                |> Array.map (fun production ->
                    // Create an 'item', with the parser position at
                    // the beginning of the production.
                    {   Nonterminal = Start;
                        Production = production;
                        Position = GenericZero;
                        Lookahead = (); })
                |> Set.ofArray
                |> Item.closure grammar.Productions

            // The initial table-gen state.
            let initialParserStateId, initialTableGenState =
                LrTableGenState.stateId initialParserState LrTableGenState.empty
            
            // Create the parser table.
            createTableImpl grammar initialTableGenState

        // Create the parser table from the table-gen state.
        {   ActionTable = finalTableGenState.ActionTable;
            GotoTable = finalTableGenState.GotoTable;
            ParserStates =
                (Map.empty, finalTableGenState.ParserStates)
                ||> Map.fold (fun parserStates state stateId ->
                    Map.add stateId state parserStates);
            ReductionRulesById = finalTableGenState.ReductionRulesById; }


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
        /// The final table-gen state.
        let finalTableGenState =
            /// The initial state (set of items) passed to 'createTable'.
            let initialParserState =
                grammar.Productions
                |> Map.find Start
                |> Array.map (fun production ->
                    // Create an 'item', with the parser position at
                    // the beginning of the production.
                    {   Nonterminal = Start;
                        Production = production;
                        Position = GenericZero;
                        Lookahead = (); })
                |> Set.ofArray
                |> Lr0.Item.closure grammar.Productions

            // The initial table-gen state.
            let initialParserStateId, initialTableGenState =
                LrTableGenState.stateId initialParserState LrTableGenState.empty
            
            // Create the parser table.
            Lr0.createTableImpl grammar initialTableGenState

        // Compute the Parser State Position Graph for each parser state.
        (Map.empty, finalTableGenState.ParserStates)
        ||> Map.fold (fun parserStatePositionGraphs parserState parserStateId ->
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


// Simple LR (SLR) parser tables.
[<RequireQualifiedAccess>]
module internal Slr =
    //
    let rec private createTableImpl (grammar : Grammar<_,_>) analysis (tableGenState : Lr0TableGenState<'Nonterminal, AugmentedTerminal<'Terminal>>) : LrParsingTable<_,_,_> =
        // Preconditions
        assert (not <| Map.isEmpty tableGenState.ParserStates)

        let tableGenState' =
            (tableGenState, tableGenState.ParserStates)
            ||> Map.fold (fun tableGenState stateItems stateId ->
                (tableGenState, stateItems)
                ||> Set.fold (fun tableGenState item ->
                    // If the parser position is at the end of the production,
                    // add a 'reduce' action for every terminal (token) in the grammar.
                    if int item.Position = Array.length item.Production then
                        // First, add this reduction rule to the table-gen state,
                        // which gives us an identifier for the rule.
                        let reductionRuleId, tableGenState =
                            LrTableGenState.reductionRuleId (item.Nonterminal, item.Production) tableGenState

                        (*  Simple LR (SLR) parsers only differ from LR(0) parsers in one way:
                            instead of creating 'reduce' actions for all terminals (tokens)
                            in the grammar, we only create them for the tokens in the FOLLOW set
                            of this item's nonterminal. *)

                        let tokens = Map.find item.Nonterminal analysis.Follow                            

                        // Add 'reduce' actions to the parser table.
                        Lr0.TableGenState.reduce stateId reductionRuleId tokens tableGenState
                        // TEMP : Discard the unit return value until we can use a monadic fold.
                        |> snd
                    else
                        // Add actions to the table based on the next symbol to be parsed.
                        match item.Production.[int item.Position] with
                        | Symbol.Terminal EndOfFile ->
                            // When the end-of-file symbol is the next to be parsed,
                            // add an 'accept' action to the table to indicate the
                            // input has been parsed successfully.
                            LrTableGenState.accept stateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Terminal (Terminal _ as token) as symbol ->                            
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Lr0.Item.goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                LrTableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a terminal (token),
                            // so add a 'shift' action to this entry of the table.
                            LrTableGenState.shift stateId token targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Nonterminal nonterm as symbol ->
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Lr0.Item.goto symbol stateItems grammar.Productions

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                LrTableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a nonterminal,
                            // so add a 'goto' action to this entry of the table.
                            LrTableGenState.goto stateId nonterm targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd
                        ))
            
        // If any states or transition-edges have been added, we need to recurse
        // and continue until we reach a fixpoint; otherwise, return the completed table.
        if tableGenState.ParserStates <> tableGenState'.ParserStates ||
            tableGenState.ActionTable <> tableGenState'.ActionTable ||
            tableGenState.GotoTable <> tableGenState'.GotoTable then
            createTableImpl grammar analysis tableGenState'
        else
            // Create the parser table from the table-gen state.
            {   ActionTable = tableGenState.ActionTable;
                GotoTable = tableGenState.GotoTable;
                ParserStates =
                    (Map.empty, tableGenState.ParserStates)
                    ||> Map.fold (fun parserStates state stateId ->
                        Map.add stateId state parserStates);
                ReductionRulesById = tableGenState.ReductionRulesById; }

    /// Creates a Simple LR (SLR) parser table from the specified grammar.
    let createTable (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) =
        /// Predictive sets of the augmented grammar.
        let analysis = PredictiveSets.ofGrammar grammar

        /// The initial state (set of items) passed to 'createTable'.
        let initialParserState =
            grammar.Productions
            |> Map.find Start
            |> Array.map (fun production ->
                // Create an 'item', with the parser position at
                // the beginning of the production.
                {   Nonterminal = Start;
                    Production = production;
                    Position = GenericZero;
                    Lookahead = (); })
            |> Set.ofArray
            |> Lr0.Item.closure grammar.Productions

        // The initial table-gen state.
        let initialParserStateId, initialTableGenState =
            LrTableGenState.stateId initialParserState LrTableGenState.empty

        // Create the parser table.
        createTableImpl grammar analysis initialTableGenState


/// Bounded right-context (BRC(1,1)) parser tables.
[<RequireQualifiedAccess>]
module internal Brc =
    /// Creates a bounded right-context (BRC(1,1)) parser table from the specified grammar.
    let createTable (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) =
        // TODO : Implement the algorithm which converts an
        // SLR(1) grammar into a BRC(1,1) grammar.
        raise <| System.NotImplementedException "Brc.createTable"


/// An LR(1) item.
type internal Lr1Item<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrItem<'Nonterminal, 'Terminal, 'Terminal>

/// An LR(1) parser state -- i.e., a set of LR(1) items.
type internal Lr1ParserState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrParserState<'Nonterminal, 'Terminal, 'Terminal>

/// LR(1) parser table generation state.
type internal Lr1TableGenState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    LrTableGenState<'Nonterminal, 'Terminal, 'Terminal>

/// LR(1) parser tables.
[<RequireQualifiedAccess>]
module internal Lr1 =
    /// Functions for manipulating LR(1) parser items.
    [<RequireQualifiedAccess>]
    module Item =
        /// Computes the FIRST set of a string of symbols.
        /// The string is a "substring" of a production, followed by a lookahead token.
        let firstSetOfString (production : Symbol<'Nonterminal, 'Terminal>[]) startIndex lookahead predictiveSets =
            // Preconditions
            if startIndex < 0 then
                invalidArg "startIndex" "The start index cannot be negative."
            elif startIndex > Array.length production then
                invalidArg "startIndex" "The start index cannot be greater than the length of the production."

            let productionLength = Array.length production

            //
            let rec firstSetOfString firstSet symbolIndex =
                // If we've reached the end of the production,
                // add the lookahead token to the set and return.
                if symbolIndex = productionLength then
                    Set.add lookahead firstSet
                else
                    // Match on the current symbol of the production.
                    match production.[symbolIndex] with
                    | Symbol.Terminal token ->
                        // Add the token to the set; then, return
                        // because tokens are never nullable.
                        Set.add token firstSet

                    | Symbol.Nonterminal nontermId ->
                        /// The FIRST set of this nonterminal symbol.
                        let nontermFirstSet = Map.find nontermId predictiveSets.First

                        // Merge the FIRST set of this nonterminal symbol into
                        // the FIRST set of the string.
                        let firstSet = Set.union firstSet nontermFirstSet

                        // If this symbol is nullable, continue processing with
                        // the next symbol in the production; otherwise, return.
                        if Map.find nontermId predictiveSets.Nullable then
                            firstSetOfString firstSet (symbolIndex + 1)
                        else
                            firstSet

            // Call the recursive implementation to compute the FIRST set.
            firstSetOfString Set.empty startIndex

        /// Computes the LR(1) closure of a set of items.
        // TODO : Modify this to use a worklist-style algorithm to avoid
        // reprocessing items which already exist in the set (i.e., when iterating,
        // we only process items added to the set in the previous iteration).
        let closure (grammar : Grammar<'Nonterminal, 'Terminal>) predictiveSets items =
            /// Implementation of the LR(1) closure algorithm.
            let rec closure items =
                let items' =
                    (items, items)
                    ||> Set.fold (fun items item ->
                        // If the position is at the end of the production,
                        // there's nothing that needs to be done for this item.
                        if int item.Position = Array.length item.Production then
                            items
                        else
                            // Determine what to do based on the next symbol to be parsed.
                            match item.Production.[int item.Position] with
                            | Symbol.Terminal _ ->
                                // Nothing to do for terminals
                                items
                            | Symbol.Nonterminal nontermId ->
                                /// The productions of this nonterminal.
                                let nontermProductions = Map.find nontermId grammar.Productions
                            
                                /// The FIRST set of the remaining symbols in this production
                                /// (i.e., the symbols following this nonterminal symbol),
                                /// plus the lookahead token from the item.
                                let firstSetOfRemainingSymbols =
                                    firstSetOfString item.Production (int item.Position + 1) item.Lookahead predictiveSets

                                // For all productions of this nonterminal, create a new item
                                // with the parser position at the beginning of the production.
                                // Add these new items into the set of items.
                                (items, nontermProductions)
                                ||> Array.fold (fun items production ->
                                    // Combine the production with each token which could
                                    // possibly follow this nonterminal.
                                    (items, firstSetOfRemainingSymbols)
                                    ||> Set.fold (fun items nontermFollowToken ->
                                        let newItem = {
                                            Nonterminal = nontermId;
                                            Production = production;
                                            Position = GenericZero;
                                            Lookahead = nontermFollowToken; }

                                        Set.add newItem items)))

                // If the items set has changed, recurse for another iteration.
                // If not, we're done processing and the set is returned.
                if items' = items then
                    items
                else
                    closure items'

            // Compute the closure, starting with the specified initial item.
            closure items

        /// Moves the 'dot' (the current parser position) past the
        /// specified symbol for each item in a set of items.
        let goto symbol items (grammar : Grammar<'Nonterminal, 'Terminal>) predictiveSets =
            /// The updated 'items' set.
            let items =
                (Set.empty, items)
                ||> Set.fold (fun updatedItems item ->
                    // If the position is at the end of the production, we know
                    // this item can't be a match, so continue to to the next item.
                    if int item.Position = Array.length item.Production then
                        updatedItems
                    else
                        // If the next symbol to be parsed in the production is the
                        // specified symbol, create a new item with the position advanced
                        // to the right of the symbol and add it to the updated items set.
                        if item.Production.[int item.Position] = symbol then
                            let updatedItem =
                                { item with
                                    Position = item.Position + 1<_>; }
                            Set.add updatedItem updatedItems
                        else
                            // The symbol did not match, so this item won't be added to
                            // the updated items set.
                            updatedItems)

            // Return the closure of the item set.
            closure grammar predictiveSets items

    /// Functions which use the State monad to manipulate an LR(1) table-generation state.
    [<RequireQualifiedAccess>]
    module TableGenState =
        /// Add a 'reduce' action to the parser table for the specified lookahead token.
        let reduce (sourceState : ParserStateId)
                    (reductionRuleId : ReductionRuleId)
                    (lookaheadToken : AugmentedTerminal<'Terminal>)
                    (tableGenState : Lr1TableGenState<'Nonterminal, AugmentedTerminal<'Terminal>>) =
            //
            let tableKey = sourceState, lookaheadToken

            //
            let entry =
                let action = LrParserAction.Reduce reductionRuleId
                match Map.tryFind tableKey tableGenState.ActionTable with
                | None ->
                    Set.singleton action
                | Some entry ->
                    Set.add action entry

            // Update the table with the new entry.
            (),
            { tableGenState with
                ActionTable = Map.add tableKey entry tableGenState.ActionTable; }


    //
    let rec private createTableImpl (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) predictiveSets (tableGenState : Lr1TableGenState<_,_>) =
        // Preconditions
        assert (not <| Map.isEmpty tableGenState.ParserStates)

        let tableGenState' =
            (tableGenState, tableGenState.ParserStates)
            ||> Map.fold (fun tableGenState stateItems stateId ->
                (tableGenState, stateItems)
                ||> Set.fold (fun tableGenState item ->
                    // If the parser position is at the end of the production,
                    // add a 'reduce' action for every terminal (token) in the grammar.
                    if int item.Position = Array.length item.Production then
                        // First, add this reduction rule to the table-gen state,
                        // which gives us an identifier for the rule.
                        let reductionRuleId, tableGenState =
                            LrTableGenState.reductionRuleId (item.Nonterminal, item.Production) tableGenState

                        // Add a 'reduce' action for the entry with this state and lookahead token.
                        TableGenState.reduce stateId reductionRuleId item.Lookahead tableGenState
                        // TEMP : Discard the unit return value until we can use a monadic fold.
                        |> snd
                    else
                        // Add actions to the table based on the next symbol to be parsed.
                        match item.Production.[int item.Position] with
                        | Symbol.Terminal EndOfFile ->
                            // When the end-of-file symbol is the next to be parsed,
                            // add an 'accept' action to the table to indicate the
                            // input has been parsed successfully.
                            LrTableGenState.accept stateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Terminal (Terminal _ as token) as symbol ->                            
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Item.goto symbol stateItems grammar predictiveSets

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                LrTableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a terminal (token),
                            // so add a 'shift' action to this entry of the table.
                            LrTableGenState.shift stateId token targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd

                        | Symbol.Nonterminal nonterm as symbol ->
                            /// The state (set of items) transitioned into
                            /// via the edge labeled with this symbol.
                            let targetState = Item.goto symbol stateItems grammar predictiveSets

                            /// The identifier of the target state.
                            let targetStateId, tableGenState =
                                LrTableGenState.stateId targetState tableGenState

                            // The next symbol to be parsed is a nonterminal,
                            // so add a 'goto' action to this entry of the table.
                            LrTableGenState.goto stateId nonterm targetStateId tableGenState
                            // TEMP : Discard the unit return value until we can use a monadic fold.
                            |> snd
                        ))
            
        // If any states or transition-edges have been added, we need to recurse
        // and continue until we reach a fixpoint; otherwise, return the completed table.
        if tableGenState.ParserStates <> tableGenState'.ParserStates ||
            tableGenState.ActionTable <> tableGenState'.ActionTable ||
            tableGenState.GotoTable <> tableGenState'.GotoTable then
            createTableImpl grammar predictiveSets tableGenState'
        else
            // Return the table-gen state itself -- the consuming method
            // can construct the table from it.
            tableGenState

    //
    let internal createTableGenState (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) =
        /// Analysis of the augmented grammar.
        let predictiveSets = PredictiveSets.ofGrammar grammar

        /// The initial state (set of items) passed to 'createTable'.
        let initialParserState : Lr1ParserState<_,_> =
            let startProductions = Map.find Start grammar.Productions
            (Set.empty, startProductions)
            ||> Array.fold (fun items production ->
                // Create an 'item', with the parser position at
                // the beginning of the production.
                let item = {
                    Nonterminal = Start;
                    Production = production;
                    Position = GenericZero;
                    // Any token can be used here, because the end-of-file symbol
                    // (in the augmented start production) will never be shifted.
                    // We use the EndOfFile token itself here to keep the code generic.
                    Lookahead = EndOfFile; }
                Set.add item items)
            |> Item.closure grammar predictiveSets

        // The initial table-gen state.
        let initialParserStateId, initialTableGenState =
            LrTableGenState.stateId initialParserState LrTableGenState.empty

        // Create the table-gen state.
        createTableImpl grammar predictiveSets initialTableGenState

    /// Create an LR(1) parser table for the specified grammar.
    let createTable (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) : LrParsingTable<_,_,_> =
        // Create the table-gen state.
        let tableGenState = createTableGenState grammar

        // Create the LR(1) parser table from the table-gen state.
        {   ActionTable = tableGenState.ActionTable;
            GotoTable = tableGenState.GotoTable;
            ParserStates =
                (Map.empty, tableGenState.ParserStates)
                ||> Map.fold (fun parserStates state stateId ->
                    Map.add stateId state parserStates);
            ReductionRulesById = tableGenState.ReductionRulesById; }
            

/// <summary>A LALR(1) parser state. This is simply an LR(1) parser state
/// (set of LR(1) items) whose lookahead tokens have been discarded.</summary>
type internal Lalr1ParserState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    Set<LrItem<'Nonterminal, 'Terminal, unit>>

/// LALR(1) parser tables.
[<RequireQualifiedAccess>]
module Lalr1 =
    /// Create a LALR(1) action from an LR(1) action.
    let private lalrAction lrToLalrIdMap lrAction =
        match lrAction with
        | LrParserAction.Shift lrParserStateId ->
            Map.find lrParserStateId lrToLalrIdMap
            |> LrParserAction.Shift
        // These actions don't change
        | LrParserAction.Reduce _
        | LrParserAction.Accept as action ->
            action

    /// Discards the lookahead tokens from the items in an LR(1) parser state.
    let private discardLookaheadTokens (lr1ParserState : Lr1ParserState<'Nonterminal, 'Terminal>)
        : Lalr1ParserState<'Nonterminal, 'Terminal> =
        lr1ParserState
        |> Set.map (fun lr1Item ->
            {   Nonterminal = lr1Item.Nonterminal;
                Production = lr1Item.Production;
                Position = lr1Item.Position;
                Lookahead = (); } : Lr0Item<_,_>)

    /// Create a LALR(1) parser table for the specified grammar.
    let createTable (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>) : LrParsingTable<_,_,_> =
        // Create the table-gen state.
        let tableGenState = Lr1.createTableGenState grammar

        // Fold over the LR(1) table-gen state to determine which LR(1) states
        // (sets of LR(1) items) are equivalent except for their lookahead
        // tokens. The resulting merged states are the LALR(1) states.
        /// Maps LR(1) state identifiers to LALR(1) state identifiers.
        let lrToLalrIdMap, lalr1ParserStates =
            ((Map.empty, Map.empty), tableGenState.ParserStates)
            // lrToLalrIdMap -- Maps LR(1) state identifiers to LALR(1) state identifiers.
            // noLookaheadStateIdMap -- Maps LR(1) states whose lookahead tokens have been
            // discarded to the LALR(1) state identifier representing that state and any
            // other equivalent states which have been merged into it.
            ||> Map.fold (fun (lrToLalrIdMap, noLookaheadStateIdMap : Map<Lalr1ParserState<_,_>, ParserStateId>) lrParserState lrParserStateId ->
                /// The LALR(1) state identifier for this LR(1) state.
                let lalrParserStateId, noLookaheadStateIdMap =
                    /// The items of this LR(1) state, without their lookahead tokens.
                    let lrParserStateNoLookahead = discardLookaheadTokens lrParserState

                    // Find the LALR(1) state id for this LR(1) state without lookahead tokens.
                    // If no state id has been created for it yet, create one and add it to the map.
                    match Map.tryFind lrParserStateNoLookahead noLookaheadStateIdMap with
                    | Some lalrParserStateId ->
                        lalrParserStateId, noLookaheadStateIdMap
                    | None ->
                        // Create a new LALR(1) state identifier for this state.
                        let lalrParserStateId : ParserStateId =
                            noLookaheadStateIdMap.Count + 1
                            |> Int32WithMeasure

                        // Add this state and it's identifier to the map.
                        let noLookaheadStateIdMap =
                            Map.add lrParserStateNoLookahead lalrParserStateId noLookaheadStateIdMap

                        // Return the state identifier and the updated map.
                        lalrParserStateId, noLookaheadStateIdMap

                // Add an entry to the LR(1) -> LALR(1) state id map.
                let lrToLalrIdMap = Map.add lrParserStateId lalrParserStateId lrToLalrIdMap                     

                // Pass the maps to the next iteration of the folds.
                lrToLalrIdMap,
                noLookaheadStateIdMap)

        // Using the LR(1) to LALR(1) state-id map, create a
        // LALR(1) parser table from the LR(1) parser table.
        let lalrActionTable =
            (Map.empty, tableGenState.ActionTable)
            ||> Map.fold (fun lalrActionTable (lrParserStateId, lookaheadToken) lrActions ->
                /// The LALR(1) state identifier for this LR(1) state.
                let lalrParserStateId = Map.find lrParserStateId lrToLalrIdMap

                /// The LALR(1) table entry for this LALR(1) state and lookahead token.
                let entry =
                    // Create LALR(1) actions from the LR(1) actions.
                    let lalrActions = Set.map (lalrAction lrToLalrIdMap) lrActions

                    // If the LALR(1) table already contains an entry for this LALR(1)
                    // state and lookahead token, merge the actions of this LR(1) state
                    // with the existing LALR(1) actions.
                    match Map.tryFind (lalrParserStateId, lookaheadToken) lalrActionTable with
                    | None ->
                        lalrActions
                    | Some entry ->
                        Set.union entry lalrActions

                // Add/update this entry in the LALR(1) ACTION table.
                Map.add (lalrParserStateId, lookaheadToken) entry lalrActionTable)

        //
        let lalrGotoTable =
            (Map.empty, tableGenState.GotoTable)
            ||> Map.fold (fun lalrGotoTable (lrParserStateId, lookaheadToken) lrTargetState ->
                /// The LALR(1) state identifier for this LR(1) state.
                let lalrParserStateId = Map.find lrParserStateId lrToLalrIdMap

                // The GOTO map shouldn't ever have overlapping entries,
                // but check (DEBUG only) to be sure.
                assert (not <| Map.containsKey (lalrParserStateId, lookaheadToken) lalrGotoTable)

                // The LALR(1) state identifer for the target state.
                let lalrTargetStateId = Map.find lrTargetState lrToLalrIdMap

                // Add this entry to the LALR(1) GOTO table.
                Map.add (lalrParserStateId, lookaheadToken) lalrTargetStateId lalrGotoTable)

        // Create and return the LALR(1) parser table.
        {   ActionTable = lalrActionTable;
            GotoTable = lalrGotoTable;
            ParserStates =
                (Map.empty, lalr1ParserStates)
                ||> Map.fold (fun parserStates state stateId ->
                    Map.add stateId state parserStates);
            ReductionRulesById = tableGenState.ReductionRulesById; }

