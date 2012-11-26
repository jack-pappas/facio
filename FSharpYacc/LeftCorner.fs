(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.LeftCorner

open Ast


/// An action which manipulates the state of the
/// parser automaton for a left-corner parser.
type LeftCornerParserAction =
    /// Shift into a state.
    | Shift of ParserStateId
    /// Goto a state.
    | Goto of ParserStateId
    /// Announce that the free position ("recognition point")
    /// has been reached for the specified rule.
    | Announce of ReductionRuleId
    /// Accept.
    | Accept

    override this.ToString () =
        match this with
        | Shift stateId ->
            "s" + stateId.ToString ()
        | Goto stateId ->
            "g" + stateId.ToString ()
        | Announce ruleId ->
            "n" + ruleId.ToString ()
        | Accept ->
            "a"


// Utility functions for generating left-corner parsers.
// module internal LeftCorner
// let [<Literal>] ihat = "\u0069\u0302"


// TODO : Implement modules for generating other types of parsers
    // Deterministic
    // SGLC -- Simple Generalized Left-Corner, accomodates SLR(1) grammars
    // XLC(1) - eXtended generalized Left-Corner(1), accomodates LR(1) grammars
    // LAXLC(1) - Look-Ahead eXtended generalized Left-Corner(1), accomodates LALR(1) grammars

    // Nondeterministic
    // GLR -- Generalized LR (perhaps as Scannerless GLR (SGLR))
    // GLC -- Generalized Left-Corner (see Nederhof, "Generalized Left-Corner Parsing")

