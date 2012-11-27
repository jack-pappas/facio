(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.LeftCorner

open Ast


/// Classifies a parser position (within a parser item), based on
/// how the insertion of a semantic routine at that position would
/// change the classification of the grammar.
type PositionClassification =
    /// No semantic routine may be called at this position.
    // Inserting a semantic routine here always causes the grammar
    // to become non-deterministic.
    | Forbidden
    /// It is sometimes safe to call a semantic routine at this position.
    // Inserting a semantic routine here may cause the grammar to
    // become non-deterministic.
    | Contingent
    /// It is always safe to call a semantic routine at this position.
    // Inserting a semantic routine here preserves the grammar class;
    // e.g., an LR(1) grammar will still be LR(1) after inserting the routine.
    | Free

//
[<RequireQualifiedAccess>]
module PositionAnalysis =
    //
    let analyze (grammar : Grammar<'NonterminalId, 'Token>) =
        // TODO : Need to implement some graph functionality (for dominators)
        // before this algorithm can be implemented.
        failwith "TODO"


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

//
type LeftCornerParserTable<'NonterminalId, 'Token
        when 'NonterminalId : comparison
        and 'Token : comparison> = {
    //
    Table : Map<ParserStateId * Symbol<'NonterminalId, 'Token>, Set<LeftCornerParserAction>>;
    //
    ParserStateCount : uint32;
    //
    ReductionRulesById : Map<ReductionRuleId, 'NonterminalId * Symbol<'NonterminalId, 'Token>[]>;
}

/// A Left-Corner parser item.
type internal LeftCornerItem<'NonterminalId, 'Token
        when 'NonterminalId : comparison
        and 'Token : comparison> = {
    //
    Nonterminal : 'NonterminalId;
    //
    Production : Symbol<'NonterminalId, 'Token>[];
    //
    Position : int<ParserPosition>;
} with
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

/// Functions for manipulating Left-Corner parser items.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal LeftCornerItem =
    /// Computes the closure of a set of Left-Corner items.
    // TODO : Modify this to use a worklist-style algorithm to avoid
    // reprocessing items which already exist in the set (i.e., when iterating,
    // we only process items added to the set in the previous iteration).
    let closure (productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>) items =
        /// Implementation of the LR(0) closure algorithm.
        let rec closure items =
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
                        | Symbol.Terminal _ ->
                            // Nothing to do for terminals
                            items
                        | Symbol.Nonterminal nontermId ->
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
    let goto symbol items (productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>) =
        /// The updated 'items' set.
        let items =
            (Set.empty, items)
            ||> Set.fold (fun updatedItems item ->
                // If the position is at the end of the production, we know
                // this item can't be a match, so continue to to the next item.
                if int item.Position = Array.length item.Production then
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
        closure productions items


/// A Left-Corner parser state -- i.e., a set of Left-Corner items.
type internal LeftCornerParserState<'NonterminalId, 'Token
        when 'NonterminalId : comparison
        and 'Token : comparison> = Set<LeftCornerItem<'NonterminalId, 'Token>>



//// Utility functions for generating left-corner parsers.
//module internal Utilities =
//    let [<Literal>] ihat = "\u0069\u0302"
//    let [<Literal>] turnstile = '\u22a2'
//    let [<Literal>] rev_turnstile = '\u22a3'


// TODO : Implement modules for generating other types of parsers
    // Deterministic
    // SGLC -- Simple Generalized Left-Corner, accomodates SLR(1) grammars
    // XLC(1) - eXtended generalized Left-Corner(1), accomodates LR(1) grammars
    // LAXLC(1) - Look-Ahead eXtended generalized Left-Corner(1), accomodates LALR(1) grammars

    // Nondeterministic
    // GLR -- Generalized LR (perhaps as Scannerless GLR (SGLR))
    // GLC -- Generalized Left-Corner (see Nederhof, "Generalized Left-Corner Parsing")

