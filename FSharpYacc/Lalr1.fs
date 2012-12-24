(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace FSharpYacc.LR

open LanguagePrimitives
open FSharpYacc.Grammar
open AugmentedPatterns
open FSharpYacc.Analysis
open FSharpYacc.Graph


/// <summary>LALR(1) parser table generator.</summary>
/// <remarks>Look-Ahead LR(1) (LALR(1)) parsing is a simplified form of LR(1) parsing;
/// it has "just enough" power to parse most languages while avoiding the huge
/// tables associated with canonical LR(1) parsers. A LALR(1) parser table has the
/// the same number of parser states (table rows) as an LR(0) or SLR(1) parser table
/// for the same grammar; the only difference is that the LALR(1) algorithm is able
/// to resolve more conflicts automatically than SLR(1) by using a more powerful algorithm
/// for computing lookaheads.</remarks>
[<RequireQualifiedAccess>]
module Lalr1 =
    module Graph = VertexLabeledSparseDigraph

    //
    type PropagationGraph<'Nonterminal, 'Terminal
        when 'Nonterminal : comparison
        and 'Terminal : comparison> =
        VertexLabeledSparseDigraph<ParserStateId * Lr0Item<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>>>

    //
    let internal propagationGraph (lr0ParsingTable : Lr0ParserTable<'Nonterminal, 'Terminal>)
        : PropagationGraph<'Nonterminal, 'Terminal> =
        /// The initial propagation graph, containing all of the vertices but no edges.
        let (propagationGraph : PropagationGraph<_,_>), itemFollow =
            ((Graph.empty, Map.empty), lr0ParsingTable.ParserStates)
            ||> Map.fold (fun propagationGraph_itemFollow stateId items ->
                (propagationGraph_itemFollow, items)
                ||> Set.fold (fun (propagationGraph, itemFollow) item ->
                    Graph.addVertex (stateId, item) propagationGraph,
                    Map.add (stateId, item) Set.empty itemFollow))

        // Build the propagation graph
        (propagationGraph, lr0ParsingTable.ParserStates)
        ||> Map.fold (fun propagationGraph stateId items ->
            



            propagationGraph)

//
//        //
//        raise <| System.NotImplementedException "Lalr1.propagationGraph"


    //
    let ofLr0Table (lr0ParsingTable : Lr0ParserTable<'Nonterminal, 'Terminal>)
        : LrParserTable<'Nonterminal, 'Terminal, _> =


        //
        raise <| System.NotImplementedException "Lalr1.ofLr0Table"


