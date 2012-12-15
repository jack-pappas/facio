(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.Grammar


/// A symbol within a context-free grammar (CFG).
type Symbol<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    /// An elementary symbol of the language described by the grammar.
    /// Terminal symbols are often called "tokens", especially when
    /// discussing lexical analysers and parsers.
    | Terminal of 'Terminal
    /// Nonterminal symbols are groups of zero or more terminal symbols;
    /// these groups are defined by the production rules of the grammar.
    | Nonterminal of 'Nonterminal

    /// <inherit />
    override this.ToString () =
        match this with
        | Terminal token ->
            token.ToString ()
        | Nonterminal nonterm ->
            nonterm.ToString ()

/// Represents nonterminals augmented with an additional nonterminal
/// representing the start production of an augmented grammar.
type AugmentedNonterminal<'Nonterminal when 'Nonterminal : comparison> =
    /// A nonterminal symbol specified by a grammar.
    | Nonterminal of 'Nonterminal
    /// Represents the start production of a grammar.
    | Start

    /// <inherit />
    override this.ToString () =
        match this with
        | Nonterminal nonterm ->
            nonterm.ToString ()
        | Start ->
            "\xabStart\xbb"

/// Represents terminals augmented with an additional terminal
/// representing the end-of-file marker.
type AugmentedTerminal<'Terminal when 'Terminal : comparison> =
    /// A terminal symbol specified by a grammar.
    | Terminal of 'Terminal
    /// Represents the end of a file being parsed.
    | EndOfFile

    /// <inherit />
    override this.ToString () =
        match this with
        | Terminal token ->
            token.ToString ()
        | EndOfFile ->
            "$"

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

/// A context-free grammar (CFG).
type Grammar<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    //
    Terminals : Set<'Terminal>;
    //
    Nonterminals : Set<'Nonterminal>;
    //
    Productions : Map<'Nonterminal, Symbol<'Nonterminal, 'Terminal>[][]>;
    //
    StartSymbol : 'Nonterminal;
} with
    /// Augments a Grammar with a special "start" symbol and the end-of-file marker.
    [<CompiledName("Augment")>]
    static member augment (grammar : Grammar<'Nonterminal, 'Terminal>)
        : AugmentedGrammar<'Nonterminal, 'Terminal> =
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
                        |> Array.map (Array.map (function
                            | Symbol.Nonterminal nontermId ->
                                Symbol.Nonterminal <| Nonterminal nontermId
                            | Symbol.Terminal token ->
                                Symbol.Terminal <| Terminal token))
                    Map.add (Nonterminal nontermId) nontermProductions productionMap)
                // Add the (only) production of the new start symbol.
                |> Map.add Start ([| startProduction |]); }

/// A grammar augmented with the "start" symbol and the end-of-file marker.
and AugmentedGrammar<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    Grammar<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>>

/// <summary>The 0-based index of a production of a nonterminal.</summary>
/// <remarks>Within the list or array containing a nonterminal's productions,
/// greater precedence is assigned to productions with lower indices --
/// unless a production has been explicitly assigned a precedence value.</remarks>
[<Measure>] type ProductionIndex
//
type ProductionId = int<ProductionIndex>

////
//type Production<'Nonterminal, 'Terminal
//        when 'Nonterminal : comparison
//        and 'Terminal : comparison> = {
//    //
//    Nonterminal : 'Nonterminal;
//    //
//    Symbols : Symbol<'Nonterminal, 'Terminal>[];
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

/// <summary>The position of a parser in a production.</summary>
/// <remarks>
/// The position corresponds to the 0-based index of the next symbol
/// to be parsed, so position values must always be within the range
/// [0, production.Length].
/// </remarks>
[<Measure>] type ParserPosition

/// Identifier for a parser state.
[<Measure>] type ParserStateIdentifier
/// Unique identifier for a parser state, e.g., when creating an LR parser table.
type ParserStateId = int<ParserStateIdentifier>

(* TODO :   Create a ProductionIndex -> ReductionRuleId map
            so we only emit code for production rules which are actually used
            to reduce items from the stack, but for Reduce actions we can still
            identify the original production rule (for diagnostic purposes). *)
(* NOTE :   We should probably just get rid of this and use ProductionIndex instead.
            Just emit code for all productions; when the user compiles the emitted
            code into a larger program, that compiler can perform dead-code elimination
            to get rid of any unused code. *)
//
[<Measure>] type ReductionRuleIdentifier
//
type ReductionRuleId = int<ReductionRuleIdentifier>

