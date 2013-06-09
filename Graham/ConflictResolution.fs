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

namespace Graham.LR

open Graham


//
[<RequireQualifiedAccess>]
module ConflictResolution =
    //
    let applyPrecedence (lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>) (settings : PrecedenceSettings)
        : Lr0ParserTable<'Nonterminal, 'Terminal> =
        /// The terminal 

        // Fold over the provided table, using the supplied precedence and
        // associativity tables to resolve conflicts wherever possible.
        (lr0ParserTable, lr0ParserTable.ActionTable)
        ||> Map.fold (fun lr0ParserTable ((_, terminalIndex) as key) actionSet ->
            // Does this state contain a conflict?
            match actionSet with
            | Action _ ->
                lr0ParserTable
            | Conflict conflict ->
                (* TODO :   Assert that 'terminalIndex' is not the index of the EndOfFile terminal.
                            The end-of-file marker is never shifted, so it shouldn't ever be involved in a conflict. *)

                // Use the precedence and associativity tables to resolve this conflict (if possible).
                // If the conflict can be resolved, use the LrParserTable.RemoveAction method
                // to remove the action(s) we're not using.
                match conflict.Shift with
                | None ->
                    (*  Reduce-reduce conflicts aren't solved with precedence/associativity --
                        instead, they must be resolved by the 'resolveConflicts' function. *)
                    lr0ParserTable

                | Some targetStateId ->
                    // TODO : Multi-way conflicts should really be handled in a better way to
                    // resolve the conflict as accurately as possible.
                    let reduceRuleId = TagSet.minElement conflict.Reductions

                    match TagMap.tryFind terminalIndex settings.TerminalPrecedence,
                          TagMap.tryFind reduceRuleId settings.RulePrecedence with
                    | None, _
                    | _, None ->
                        // If the precedence/associativity isn't defined for either the terminal
                        // or the production rule, we'll have to handle the conflict using the
                        // default conflict-resolving rules.
                        lr0ParserTable
                    | Some (terminalAssociativity, terminalPrecedence), Some (_, rulePrecedence) ->
                        // The conflict can be resolved if the precedences are different --
                        // we remove the action with lower precedence from this action set. 
                        if terminalPrecedence < rulePrecedence then
                            LrParserTable.RemoveAction (lr0ParserTable, key, Shift targetStateId)
                        elif terminalPrecedence > rulePrecedence then
                            LrParserTable.RemoveAction (lr0ParserTable, key, Reduce reduceRuleId)
                        else
                            // The precedences are the same, so we use the terminal's
                            // associativity to resolve the conflict.
                            match terminalAssociativity with
                            | Left ->
                                // For left-associative tokens, reduce (remove the Shift action).
                                LrParserTable.RemoveAction (lr0ParserTable, key, Shift targetStateId)
                            | Right ->
                                // For right-associative tokens, shift (remove the Reduce action).
                                LrParserTable.RemoveAction (lr0ParserTable, key, Reduce reduceRuleId)
                            | NonAssociative ->
                                // For non-associative tokens, remove *both* actions.
                                { lr0ParserTable with
                                    ActionTable = Map.remove key lr0ParserTable.ActionTable; })

    //
    let resolveConflicts (lr0ParserTable : Lr0ParserTable<'Nonterminal, 'Terminal>) =
        //
        (lr0ParserTable, lr0ParserTable.ActionTable)
        ||> Map.fold (fun lr0ParserTable key actionSet ->
            // Does this state contain a conflict?
            match actionSet with
            | Action _ ->
                lr0ParserTable
            | Conflict conflict ->
                // Use the precedence and associativity tables to resolve this conflict (if possible).
                // If the conflict can be resolved, use the LrParserTable.RemoveAction method
                // to remove the action we're not using.
                match conflict.Shift with
                | Some _ ->
                    // Resolve in favor of shifting; this is similar to the
                    // "longest match rule" used in lexical analyzers.
                    // Remove all of the reduce actions from the table.
                    (lr0ParserTable, conflict.Reductions)
                    ||> TagSet.fold (fun lr0ParserTable productionRuleId ->
                        LrParserTable.RemoveAction (lr0ParserTable, key, Reduce productionRuleId))

                | None ->
                    // Resolve in favor of the lowest-numbered rule (i.e., the rule declared first in the grammar).
                    // OPTIMIZE : Use TagSet.extractMin from ExtCore once it's implemented.
                    let resolvedRule = TagSet.minElement conflict.Reductions
                    let reductions = TagSet.remove resolvedRule conflict.Reductions
                    (lr0ParserTable, reductions)
                    ||> TagSet.fold (fun lr0ParserTable productionRuleId ->
                        LrParserTable.RemoveAction (lr0ParserTable, key, Reduce productionRuleId)))


