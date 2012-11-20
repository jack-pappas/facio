(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.Tables

open Ast
open Derivation


//
[<Measure>] type LrParsingState
//
type LrParsingStateId = int<LrParsingState>

//
[<Measure>] type LrParsingRule
//
type LrParsingRuleId = int<LrParsingRule>

//
type LrParsingTableEntry =
    /// Shift into a state.
    | Shift of LrParsingStateId
    /// Goto a state.
    | Goto of LrParsingStateId
    /// Reduce by a rule.
    | Reduce of LrParsingRuleId
    /// Accept.
    | Accept

//
type LrParsingTable<'NonterminalId, 'Token
        when 'NonterminalId : comparison
        and 'Token : comparison> = {
    //
    Table : Map<LrParsingStateId * Symbol<'NonterminalId, 'Token>, LrParsingTableEntry>;
}

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LrParsingTable =
    //
    let empty : LrParsingTable<'NonterminalId, 'Token> = {
        Table = Map.empty; }

    //
    let inline tryFind state symbol (table : LrParsingTable<'NonterminalId, 'Token>) =
        Map.tryFind (state, symbol) table.Table

    //
    let inline add state symbol entry (table : LrParsingTable<'NonterminalId, 'Token>) =
        { table with
            Table = Map.add (state, symbol) entry table.Table; }


/// Represents the position of a parser in a production.
/// The position corresponds to the 0-based index of the next symbol
/// to be parsed, so position values must always be within the range
/// [0, production.Length].
[<Measure>] type ParserPosition

//
[<RequireQualifiedAccess>]
module Lr0 =
    //
    type private Lr0Item<'NonterminalId, 'Token
            when 'NonterminalId : comparison
            and 'Token : comparison> = {
        //
        Nonterminal : 'NonterminalId;
        //
        Production : Symbol<'NonterminalId, 'Token>[];
        //
        Position : int<ParserPosition>;
    }
    
    /// Computes the LR(0) closure of a set of items.
    let private closure items (productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>) =
        /// Implementation of the LR(0) closure algorithm.
        let rec closure (items : Set<_>) =
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
                        | Terminal _ ->
                            // Nothing to do for terminals
                            items
                        | Nonterminal nontermId ->
                            /// The productions of this nonterminal.
                            let nontermProductions = Map.find nontermId productions

                            // For all productions of this nonterminal, create a new item
                            // with the parser position at the beginning of the production.
                            // Add these new items into the set of items.
                            (items, nontermProductions)
                            ||> Set.fold (fun items production ->
                                let newItem = {
                                    Nonterminal = nontermId;
                                    Production = production;
                                    Position = 0<_>; }

                                Set.add newItem items))

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
    let private goto symbol items (productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>) =
        /// The updated 'items' set.
        let items =
            (Set.empty, items)
            ||> Set.fold (fun updatedItems item ->
                /// The length of the production.
                let productionLength = Array.length item.Production

                // If the position is at the end of the production, we know
                // this item can't be a match, so continue to to the next item.
                if int item.Position = productionLength then
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
        closure items productions

 

//    let test (grammar : Grammar<_,_>) =
//        let state3StartItem = {
//            Nonterminal = 'S';
//            Production =
//                [|
//                Ast.Terminal "(";
//                Ast.Nonterminal 'L';
//                Ast.Terminal ")"; |]
//            Position = 1<_>; }
//
//        let state3Closure =
//            closure (Set.singleton state3StartItem) grammar.Productions
//
//        ()
