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
    let ofLr0Table (lr0ParsingTable : Lr0ParserTable<'Nonterminal, 'Terminal>)
        : LrParserTable<'Nonterminal, 'Terminal, _> =


        //
        raise <| System.NotImplementedException "Lalr1.ofLr0Table"


