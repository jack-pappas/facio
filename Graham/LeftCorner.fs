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
    | Announce of ProductionRuleId
    /// Accept.
    | Accept

    /// <inherit />
    override this.ToString () =
        match this with
        | Shift stateId ->
            "s" + stateId.ToString ()
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
    ParserStates : Map<ParserStateId, LeftCornerParserState<'Nonterminal, 'Terminal>>;
    //
    ActionTable : Map<ParserStateId * 'Terminal, Set<LeftCornerParserAction>>;
    //
    GotoTable : Map<ParserStateId * 'Nonterminal, ParserStateId>;    
}

/// Parser-generators for left-corner grammars.
[<RequireQualifiedAccess>]
module internal LeftCorner =
    open Graham.LR

    /// Adapts a LALR(1) parser table into an LC(1) parser table.
    let ofLalr1 (lalr1Table : LrParserTable<'Nonterminal, 'Terminal, 'Terminal>) =
        notImpl "LeftCorner.ofLalr1"

