(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.Ast


/// A symbol within a context-free grammar (CFG).
type Symbol<'NonterminalId, 'Token
                when 'NonterminalId : comparison
                and 'Token : comparison> =
    //
    | Terminal of 'Token
    //
    | Nonterminal of 'NonterminalId

    override this.ToString () =
        match this with
        | Terminal token ->
            token.ToString ()
        | Nonterminal nonterm ->
            nonterm.ToString ()

//
[<Measure>] type ProductionIndex
//
type ProductionId = int<ProductionIndex>

/// A context-free grammar (CFG).
type Grammar<'NonterminalId, 'Token
                when 'NonterminalId : comparison
                and 'Token : comparison> = {
    //
    Terminals : Set<'Token>;
    //
    Nonterminals : Set<'NonterminalId>;
    //
    Productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>;
    //
    StartSymbol : 'NonterminalId;
}

////
//type Production<'NonterminalId, 'Token
//        when 'NonterminalId : comparison
//        and 'Token : comparison> = {
//    //
//    Nonterminal : 'NonterminalId;
//    //
//    Symbols : Symbol<'NonterminalId, 'Token>[];
//} with
//    override this.ToString () =
//        let sb = System.Text.StringBuilder ()
//
//        // Add the nonterminal text and arrow to the StringBuilder.
//        sprintf "%O \u2192 " this.Nonterminal
//        |> sb.Append |> ignore
//
//        // Append the symbols
//        this.Symbols
//        |> Array.iter (fun symbol ->
//            symbol.ToString ()
//            |> sb.Append |> ignore)
//
//        sb.ToString ()

/// Represents nonterminals augmented with an additional nonterminal
/// representing the start production of an augmented grammar.
type AugmentedNonterminal<'NonterminalId when 'NonterminalId : comparison> =
    /// A nonterminal specified in the original grammar.
    | Nonterminal of 'NonterminalId
    /// Represents the start production of the grammar.
    | Start

    override this.ToString () =
        match this with
        | Nonterminal nonterm ->
            nonterm.ToString ()
        | Start ->
            "\xabStart\xbb"

//
type AugmentedTerminal<'Token when 'Token : comparison> =
    //
    | Terminal of 'Token
    //
    | EndOfFile

    override this.ToString () =
        match this with
        | Terminal token ->
            token.ToString ()
        | EndOfFile ->
            "$"

//
[<RequireQualifiedAccess>]
module AugmentedGrammar =
    //
    let ofGrammar (grammar : Grammar<'NonterminalId, 'Token>)
        : Grammar<AugmentedNonterminal<'NonterminalId>, AugmentedTerminal<'Token>> =
        // Based on the input grammar, create a new grammar with an additional
        // nonterminal and production for the start symbol and an additional token
        // representing the end-of-file marker.
        let startProduction = [|
            Symbol.Nonterminal <| Nonterminal grammar.StartSymbol;
            Symbol.Terminal EndOfFile; |]

        {   StartSymbol = Start;
            Terminals =
                grammar.Terminals
                |> Set.map Terminal
                |> Set.add EndOfFile;
            Nonterminals =
                grammar.Nonterminals
                |> Set.map Nonterminal
                |> Set.add Start;
            Productions =
                (Map.empty, grammar.Productions)
                ||> Map.fold (fun productionMap nontermId nontermProductions ->
                    let nontermProductions =
                        nontermProductions
                        |> Set.map (Array.map (function
                            | Symbol.Nonterminal nontermId ->
                                Symbol.Nonterminal <| Nonterminal nontermId
                            | Symbol.Terminal token ->
                                Symbol.Terminal <| Terminal token))
                    Map.add (Nonterminal nontermId) nontermProductions productionMap)
                // Add the (only) production of the new start symbol.
                |> Map.add Start (Set.singleton startProduction); }

/// Associativity of a terminal (token).
/// This can be explicitly specified to override the
/// default behavior for resolving conflicts.
type Associativity =
    /// Non-associative.
    | NonAssociative
    /// Left-associative.
    | Left
    /// Right-associative.
    | Right

/// Represents the position of a parser in a production.
/// The position corresponds to the 0-based index of the next symbol
/// to be parsed, so position values must always be within the range
/// [0, production.Length].
[<Measure>] type ParserPosition

//
[<Measure>] type ParserStateIdentifier
//
type ParserStateId = int<ParserStateIdentifier>

