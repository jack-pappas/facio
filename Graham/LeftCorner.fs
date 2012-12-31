(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace Graham.LeftCorner

open Graham.Grammar
open Graham.Analysis


/// An action which manipulates the state of the
/// parser automaton for a left-corner parser.
type LeftCornerParserAction =
    /// Shift into a state.
    | Shift of ParserStateId
    /// Announce that the free position ("recognition point")
    /// has been reached for the specified rule.
    | Announce of ReductionRuleId
    /// Accept.
    | Accept

    /// <inherit />
    override this.ToString () =
        match this with
        | Shift stateId ->
            "s" + stateId.ToString ()
//        | Goto stateId ->
//            "g" + stateId.ToString ()
        | Announce ruleId ->
            "n" + ruleId.ToString ()
        | Accept ->
            "a"

//// Utility functions for generating left-corner parsers.
//module internal Utilities =
//    let [<Literal>] ihat = "\u0069\u0302"
//    let [<Literal>] turnstile = '\u22a2'
//    let [<Literal>] rev_turnstile = '\u22a3'

/// A Left-Corner parser item.
type LeftCornerItem<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    //
    Nonterminal : 'Nonterminal;
    //
    Production : Symbol<'Nonterminal, 'Terminal>[];
    //
    Position : int<ParserPosition>;
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

        sb.ToString ()

/// A Left-Corner parser state -- i.e., a set of Left-Corner items.
type LeftCornerParserState<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    Set<LeftCornerItem<'Nonterminal, 'Terminal>>

//
type LeftCornerParserTable<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    //
    ActionTable : Map<ParserStateId * 'Terminal, Set<LeftCornerParserAction>>;
    //
    GotoTable : Map<ParserStateId * 'Nonterminal, ParserStateId>;
    //
    ParserStates : Map<ParserStateId, LeftCornerParserState<'Nonterminal, 'Terminal>>;
    //
    ReductionRulesById : Map<ReductionRuleId, 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]>;
}

/// Parser-generators for left-corner grammars.
[<RequireQualifiedAccess>]
module internal LeftCorner =
    open Graham.LR

    /// Adapts a LALR(1) parser table into an LC(1) parser table.
    let ofLalr1 (lalr1Table : LrParserTable<'Nonterminal, 'Terminal, 'Terminal>) =
        raise <| System.NotImplementedException "LeftCorner.ofLalr1"

