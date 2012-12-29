(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

/// Parser table generators for LR(k) grammars.
namespace FSharpYacc.LR

open LanguagePrimitives
open FSharpYacc.Grammar
open AugmentedPatterns
open FSharpYacc.Analysis
open FSharpYacc.Graph


/// An LR(k) item.
type internal LrItem<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    Nonterminal : 'Nonterminal;
    //
    Production : Symbol<'Nonterminal, 'Terminal>[];
    //
    Position : int<ParserPosition>;
    //
    Lookahead : 'Lookahead;
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

        // Append the lookahead symbol, if applicable.
        if typeof<'Lookahead> <> typeof<unit> then
            sprintf ", %A" this.Lookahead
            |> sb.Append |> ignore

        sb.ToString ()

/// An LR(k) parser state -- i.e., a set of LR(k) items.
type internal LrParserState<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> =
    Set<LrItem<'Nonterminal, 'Terminal, 'Lookahead>>

/// An action which manipulates the state of the
/// parser automaton for an LR(k) parser.
type LrParserAction =
    /// Shift into a state.
    | Shift of ParserStateId
    /// Reduce by a production rule.
    | Reduce of ReductionRuleId
    /// Accept.
    | Accept

    /// <inherit />
    override this.ToString () =
        match this with
        | Shift stateId ->
            "s" + stateId.ToString ()
        | Reduce ruleId ->
            "r" + ruleId.ToString ()
        | Accept ->
            "a"

/// LR(k) parser table generation state.
type internal LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    ParserStateIds : Map<LrParserState<'Nonterminal, 'Terminal, 'Lookahead>, ParserStateId>;
    //
    ParserTransitions : LabeledSparseDigraph<ParserStateId, Symbol<'Nonterminal, 'Terminal>>;
    //
    ActionTable : Map<ParserStateId * 'Terminal, Set<LrParserAction>>;
    //
    GotoTable : Map<ParserStateId * 'Nonterminal, ParserStateId>;

    (* TODO :   Remove these in favor of using ProductionKey in the LrParserAction.Reduce case. *)
    //
    ReductionRules : Map<'Nonterminal * Symbol<'Nonterminal, 'Terminal>[], ReductionRuleId>;
    //
    ReductionRulesById : Map<ReductionRuleId, 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]>;
}

/// Functions which use the State monad to manipulate an LR(k) table-generation state.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal LrTableGenState =
    module Graph = LabeledSparseDigraph

    /// Returns an empty Lr0TableGenState with the given
    /// nonterminal and terminal types.
    let empty : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead> = {
        ParserStateIds = Map.empty;
        ParserTransitions = Graph.empty;
        ActionTable = Map.empty;
        GotoTable = Map.empty;
        ReductionRules = Map.empty;
        ReductionRulesById = Map.empty; }

    /// Retrives the identifier for a given parser state (set of items).
    /// If the state has not been assigned an identifier, one is created
    /// and added to the table-generation state before returning.
    let stateId
        (parserState : LrParserState<'Nonterminal, 'Terminal, 'Lookahead>)
        (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        // Try to retrieve an existing id for this state.
        match Map.tryFind parserState tableGenState.ParserStateIds with
        | Some parserStateId ->
            parserStateId, tableGenState

        | None ->
            // Create a new ID for this state.
            let parserStateId =
                tableGenState.ParserStateIds.Count + 1
                |> Int32WithMeasure

            // Return the id, along with the updated table-gen state.
            parserStateId,
            { tableGenState with
                ParserStateIds =
                    Map.add parserState parserStateId tableGenState.ParserStateIds;
                // Add this state to the transition graph's vertex-set.
                ParserTransitions = Graph.addVertex parserStateId tableGenState.ParserTransitions; }

    //
    let reductionRuleId
        (reductionRule : 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[])
        (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        // Reduction rules should only be added, but for safety we'll check to
        // see if the rule has already been assigned an identifier.
        match Map.tryFind reductionRule tableGenState.ReductionRules with
        | Some reductionRuleId ->
            reductionRuleId, tableGenState

        | None ->
            // Create a new ID for this reduction rule.
            let reductionRuleId =
                tableGenState.ReductionRules.Count + 1
                |> Int32WithMeasure

            // Return the id, along with the updated table-gen state.
            reductionRuleId,
            { tableGenState with
                ReductionRules =
                    Map.add reductionRule reductionRuleId tableGenState.ReductionRules;
                ReductionRulesById =
                    Map.add reductionRuleId reductionRule tableGenState.ReductionRulesById; }

    /// Add a 'shift' action to the parser table.
    let shift (sourceState : ParserStateId)
                (transitionSymbol : 'Terminal)
                (targetState : ParserStateId)
                (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        //
        let tableKey = sourceState, transitionSymbol

        //
        let entry =
            let action = LrParserAction.Shift targetState
            match Map.tryFind tableKey tableGenState.ActionTable with
            | None ->
                Set.singleton action
            | Some entry ->
                Set.add action entry

        (),
        { tableGenState with
            // Update the table with the new entry.
            ActionTable = Map.add tableKey entry tableGenState.ActionTable;
            // Add an edge labeled with this symbol to the transition graph.
            ParserTransitions =
                tableGenState.ParserTransitions
                |> Graph.addEdge sourceState targetState (Symbol.Terminal transitionSymbol); }

    /// Add a 'goto' action to the parser table.
    let goto (sourceState : ParserStateId)
                (transitionSymbol : 'Nonterminal)
                (targetState : ParserStateId)
                (tableGenState : LrTableGenState<'Nonterminal, 'Terminal, 'Lookahead>) =
        //
        let tableKey = sourceState, transitionSymbol

        //
        match Map.tryFind tableKey tableGenState.GotoTable with
        | None ->
            (),
            { tableGenState with
                // Update the table with the new entry.
                GotoTable = Map.add tableKey targetState tableGenState.GotoTable;
                // Add an edge labelled with this symbol to the transition graph.
                ParserTransitions =
                    tableGenState.ParserTransitions
                    |> Graph.addEdge sourceState targetState (Symbol.Nonterminal transitionSymbol); }

        | Some entry ->
            // If the existing entry is the same as the target state,
            // there's nothing to do -- just return the existing 'tableGenState'.
            if entry = targetState then
                (), tableGenState
            else
                let msg = sprintf "Cannot add the entry (g%i) to the GOTO table; \
                                    it already contains an entry (g%i) for the key %A."
                                    (int targetState) (int entry) tableKey
                raise <| exn msg        

    /// Add an 'accept' action to the parser table.
    let accept (sourceState : ParserStateId) (tableGenState : LrTableGenState<'Nonterminal, AugmentedTerminal<'Terminal>, 'Lookahead>) =
        //
        let tableKey = sourceState, EndOfFile

        //
        let entry =
            match Map.tryFind tableKey tableGenState.ActionTable with
            | None ->
                // Create a new 'accept' action for this table entry.
                Set.singleton LrParserAction.Accept
            | Some entry ->
                // Create a new 'accept' action and add it to the existing table entry.
                Set.add LrParserAction.Accept entry

        // Update the table with the new entry.
        (),
        { tableGenState with
            ActionTable = Map.add tableKey entry tableGenState.ActionTable; }


//
type NonterminalTransition<'Nonterminal
    when 'Nonterminal : comparison> =
    ParserStateId * 'Nonterminal

//
type TerminalTransition<'Terminal
    when 'Terminal : comparison> =
    ParserStateId * 'Terminal

/// LR(k) parser table.
type LrParserTable<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    //
    ParserStates : Map<ParserStateId, LrParserState<'Nonterminal, 'Terminal, 'Lookahead>>;
    //
    ParserTransitions : LabeledSparseDigraph<ParserStateId, Symbol<'Nonterminal, 'Terminal>>;
    //
    ActionTable : Map<TerminalTransition<'Terminal>, Set<LrParserAction>>;
    //
    GotoTable : Map<NonterminalTransition<'Nonterminal>, ParserStateId>;

    (* TODO :   Remove this in favor of using ProductionKey in the LrParserAction.Reduce case. *)
    //
    ReductionRulesById : Map<ReductionRuleId, 'Nonterminal * Symbol<'Nonterminal, 'Terminal>[]>;
}

