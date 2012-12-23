(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace FSharpYacc.LR.Lalr1

open LanguagePrimitives
open FSharpYacc.Grammar
open AugmentedPatterns
open FSharpYacc.Analysis
open FSharpYacc.Graph
open FSharpYacc.LR
open FSharpYacc.LR.Lr0


/// <summary>A LALR(1) parser state. This is simply an LR(1) parser state
/// (set of LR(1) items) whose lookahead tokens have been discarded.</summary>
type internal Lalr1ParserState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    Set<LrItem<'Nonterminal, 'Terminal, unit>>

/// LALR(1) parser tables.
[<RequireQualifiedAccess>]
module Lalr1 =
    //




    //
    let ofLr0Table (lr0ParsingTable : Lr0ParserTable<'Nonterminal, 'Terminal>)
        : LrParserTable<'Nonterminal, 'Terminal, _> =


        //
        raise <| System.NotImplementedException "Lalr1.ofLr0Table"


