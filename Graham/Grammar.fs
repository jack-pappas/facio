(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace Graham.Grammar

open System.Diagnostics


/// A nonterminal or the start symbol.
type AugmentedNonterminal<'Nonterminal when 'Nonterminal : comparison> =
    /// The start symbol.
    | Start
    /// A nonterminal symbol specified by a grammar.
    | Nonterminal of 'Nonterminal

    /// <inherit />
    override this.ToString () =
        match this with
        | Start ->
            "\xabStart\xbb"
        | Nonterminal nonterm ->
            nonterm.ToString ()        

/// A terminal (token) or the end-of-file marker.
type AugmentedTerminal<'Terminal when 'Terminal : comparison> =
    /// A terminal symbol specified by a grammar.
    | Terminal of 'Terminal
    /// The end-of-file marker.
    | EndOfFile

    /// <inherit />
    override this.ToString () =
        match this with
        | Terminal token ->
            token.ToString ()
        | EndOfFile ->
            "$"

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

/// A symbol within a context-free grammar (CFG) augmented with
/// the start symbol and end-of-file marker.
type AugmentedSymbol<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    Symbol<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>>

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
} with
    /// <summary>Augments a Grammar with a unique "start" symbol and the end-of-file marker.</summary>
    /// <param name="grammar">The grammar to be augmented.</param>
    /// <param name="startSymbol">The parser will begin parsing with this symbol.</param>
    /// <returns>A grammar augmented with the Start symbol and the EndOfFile marker.</returns>
    static member Augment (grammar : Grammar<'Nonterminal, 'Terminal>, startSymbol : 'Nonterminal)
        : AugmentedGrammar<'Nonterminal, 'Terminal> =
        // Based on the input grammar, create a new grammar with an additional
        // nonterminal and production for the start symbol and an additional token
        // representing the end-of-file marker.
        let startProduction = [|
            Symbol.Nonterminal <| AugmentedNonterminal.Nonterminal startSymbol;
            Symbol.Terminal EndOfFile; |]

        {   Terminals =
                grammar.Terminals
                |> Set.map AugmentedTerminal.Terminal
                |> Set.add EndOfFile;
            Nonterminals =
                grammar.Nonterminals
                |> Set.map AugmentedNonterminal.Nonterminal
                |> Set.add Start;
            Productions =
                (Map.empty, grammar.Productions)
                ||> Map.fold (fun productionMap nontermId nontermProductions ->
                    let nontermProductions =
                        nontermProductions
                        |> Array.map (Array.map (function
                            | Symbol.Nonterminal nontermId ->
                                Symbol.Nonterminal <| AugmentedNonterminal.Nonterminal nontermId
                            | Symbol.Terminal token ->
                                Symbol.Terminal <| AugmentedTerminal.Terminal token))
                    Map.add (AugmentedNonterminal.Nonterminal nontermId) nontermProductions productionMap)
                // Add the (only) production of the new start symbol.
                |> Map.add Start ([| startProduction |]); }

/// A grammar augmented with the "start" symbol and the end-of-file marker.
and AugmentedGrammar<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    Grammar<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>>

//
[<Measure>] type ProductionIdx
/// <summary>The 0-based index of a production of a nonterminal.</summary>
/// <remarks>Within the list or array containing a nonterminal's productions,
/// greater precedence is assigned to productions with lower indices --
/// unless a production has been explicitly assigned a precedence value.</remarks>
type ProductionIndex = int<ProductionIdx>

//
type ProductionKey<'Nonterminal
    when 'Nonterminal : comparison> =
    'Nonterminal * ProductionIndex

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

/// Active patterns which simplify pattern matching on augmented grammars.
module AugmentedPatterns =
    let inline internal (|Nonterminal|Start|) (augmentedNonterminal : AugmentedNonterminal<'Nonterminal>) =
        match augmentedNonterminal with
        | AugmentedNonterminal.Nonterminal nonterminal ->
            Nonterminal nonterminal
        | AugmentedNonterminal.Start ->
            Start

    let inline internal (|Terminal|EndOfFile|) (augmentedTerminal : AugmentedTerminal<'Terminal>) =
        match augmentedTerminal with
        | AugmentedTerminal.Terminal terminal ->
            Terminal terminal
        | AugmentedTerminal.EndOfFile ->
            EndOfFile


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

    /// <inherit />
    override this.ToString () =
        match this with
        | NonAssociative ->
            "NonAssociative"
        | Left ->
            "Left"
        | Right ->
            "Right"

//
[<Measure>] type AbsolutePrecedence
//
type PrecedenceLevel = int<AbsolutePrecedence>

(* TODO :   Un-comment the RelativePrecedence type whenever we get around to
            implementing the algorithm for creating operator-precedence parsers. *)
(*
//
[<DebuggerDisplay("{DebuggerDisplay,nq}")>]
type RelativePrecedence =
    //
    | LessThan
    //
    | Equal
    //
    | GreaterThan

    //
    member private this.DebuggerDisplay
        with get () =
            match this with
            | LessThan ->
                "\u22d6"
            | Equal ->
                "\u2250"
            | GreaterThan ->
                "\u22d7"

    /// <inherit />
    override this.ToString () =
        match this with
        | LessThan ->
            "LessThan"
        | Equal ->
            "Equal"
        | GreaterThan ->
            "GreaterThan"

    //
    static member Inverse prec =
        match prec with
        | LessThan ->
            GreaterThan
        | Equal ->
            Equal
        | GreaterThan ->
            LessThan
*)

