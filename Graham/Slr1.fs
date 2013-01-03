(*
Copyright (c) 2012, Jack Pappas
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
    let upgrade (grammar : AugmentedGrammar<'Nonterminal, 'Terminal>, lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>) =
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
                if int item.Position = Array.length item.Production then
                    /// The rule nonterminal's FOLLOW set.
                    let nonterminalFollow =
                        Map.find item.Nonterminal predictiveSets.Follow

                    // Remove the unnecessary Reduce actions, thereby resolving some conflicts.
                    let actionTable =
                        let action =
                            parserTable.ReductionRulesById
                            // OPTIMIZE : This lookup is slow (O(n)) -- we should use a Bimap instead.
                            |> Map.pick (fun ruleId key ->
                                if key = (item.Nonterminal, item.Production) then
                                    Some ruleId
                                else None)
                            |> LrParserAction.Reduce
                        (parserTable.ActionTable, grammar.Terminals)
                        ||> Set.fold (fun actionTable terminal ->
                            // Is this terminal in the nonterminal's FOLLOW set?
                            if Set.contains terminal nonterminalFollow then
                                actionTable
                            else
                                //
                                let tableKey = stateId, terminal

                                // Don't need to do anything if there's no entry for this key;
                                // it may mean that the table has already been upgraded.
                                match Map.tryFind tableKey actionTable with
                                | None ->
                                    actionTable
                                | Some entry ->
                                    // Remove the Reduce action from the action set.
                                    match LrParserActionSet.Remove action entry with
                                    | None ->
                                        // The remaining action set is empty -- so just
                                        // remove the existing entry from the table.
                                        Map.remove tableKey actionTable
                                    | Some entry ->
                                        // Update the ACTION table with the modified action set.
                                        Map.add tableKey entry actionTable)

                    // Pass the modified parser table to the next iteration.
                    { parserTable with ActionTable = actionTable; }
                else
                    parserTable))


