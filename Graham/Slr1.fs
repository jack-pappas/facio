(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace Graham.LR

open LanguagePrimitives
open Graham.Grammar
open AugmentedPatterns
open Graham.Analysis
open Graham.Graph


/// <summary>SLR(1) parser table generator.</summary>
/// <remarks>Simple LR (SLR) is more powerful than LR(0), but less powerful
/// than either LR(1) or LALR(1). An SLR(1) parser table will have the same
/// number of parser states (table rows) as an LR(0) parser table for a
/// given grammar; the only difference is that SLR(1) uses the FOLLOW sets
/// of the grammar's nonterminals to resolve some conflicts automatically.</remarks>
[<RequireQualifiedAccess>]
module Slr1 =
    /// Given a grammar and it's LR(0) parser table, upgrades the table to SLR(1).
    let upgrade (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>,
                 lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>,
                 productionRuleIds : Map<(AugmentedNonterminal<'Nonterminal> * AugmentedSymbol<'Nonterminal, 'Terminal>[]), ProductionRuleId>) =
        /// Predictive sets of the augmented grammar.
        let predictiveSets = PredictiveSets.ofGrammar grammar

        // Upgrade the LR(0) parser table to SLR(1).
        // If the table has already been upgraded to SLR(1) (or something
        // more powerful, like LALR(1)), this has no effect.
        (lr0ParserTable, lr0ParserTable.ParserStates)
        ||> Map.fold (fun parserTable stateId items ->
            (parserTable, items)
            ||> Set.fold (fun parserTable item ->
                // If the parser position is at the end of this item's production,
                // remove the Reduce actions from the ACTION table for any tokens
                // which aren't in this nonterminal's FOLLOW set.
                if int item.Position < Array.length item.Production then
                    parserTable
                else
                    /// The rule nonterminal's FOLLOW set.
                    let nonterminalFollow =
                        Map.find item.Nonterminal predictiveSets.Follow

                    // Remove the unnecessary Reduce actions, thereby resolving some conflicts.
                    let action =
                        productionRuleIds
                        |> Map.find (item.Nonterminal, item.Production)
                        |> LrParserAction.Reduce

                    (parserTable, grammar.Terminals)
                    ||> Set.fold (fun parserTable terminal ->
                        // Is this terminal in the nonterminal's FOLLOW set?
                        if Set.contains terminal nonterminalFollow then
                            parserTable
                        else
                            // Remove the unnecessary Reduce action for this terminal.
                            let key = stateId, terminal
                            LrParserTable.RemoveAction (parserTable, key, action))
                            ))


