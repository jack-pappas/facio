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

namespace FSharpYacc.Plugin.FsYacc

open System.CodeDom.Compiler
open System.ComponentModel.Composition
open System.IO
open LanguagePrimitives
open FSharpYacc
open FSharpYacc.Ast
open FSharpYacc.Compiler
open FSharpYacc.Plugin


/// Helper functions for emitting F# code into an IndentedTextWriter.
// TODO : Move this into the BackendUtils project, it could be re-used elsewhere.
[<AutoOpen>]        //[<RequireQualifiedAccess>]
module private Emit =
    open BackendUtils.CodeGen

    /// Emit a formatted string as a single-line F# comment into an IndentedTextWriter.
    let inline comment (writer : IndentedTextWriter) fmt : ^T =
        writer.Write "// "
        fprintfn writer fmt

    /// Emits a formatted string as a quick-summary (F# triple-slash comment) into an IndentedTextWriter.
    let inline quickSummary (writer : IndentedTextWriter) fmt : ^T =
        fmt |> Printf.ksprintf (fun str ->
            // OPTIMIZE : Use the String.Split.iter function from ExtCore.
            // Split the string into individual lines.
            str.Split ([| "\r\n"; "\r"; "\n" |], System.StringSplitOptions.None)
            // Write the lines to the IndentedTextWriter as triple-slash comments.
            |> Array.iter (fun line ->
                writer.Write "/// "
                writer.WriteLine (line.Trim ())
                ))

    /// <summary>Emits the declaration of a discriminated union type into an IndentedTextWriter.</summary>
    /// <param name="typeName">The name of the type.</param>
    /// <param name="isPublic">When set, the type will be publicly-visible.</param>
    /// <param name="cases">A map containing the names (and types, if applicable) of the cases.</param>
    /// <param name="writer">The IndentedTextWriter into which to write the code.</param>
    let unionTypeDecl (typeName : string) isPublic (cases : Map<string, string option>) (writer : IndentedTextWriter) =
        // Write the type declaration
        if isPublic then
            sprintf "type %s =" typeName
        else
            sprintf "type private %s =" typeName
        |> writer.WriteLine

        // Write the type cases
        IndentedTextWriter.indented writer <| fun writer ->
            cases
            |> Map.iter (fun caseName caseType ->
                match caseType with
                | None ->
                    "| " + caseName
                | Some caseType ->
                    // NOTE : The parentheses here are actually quite important -- if the token type
                    // is a tuple, then wrapping it in parenthesis makes the F# compiler treat it as
                    // a single value. This reduces performance, but makes emitting some of the
                    // pattern-matching clauses in the other functions much simpler.
                    sprintf "| %s of (%s)" caseName caseType
                |> writer.WriteLine)

    /// Emits code which declares a literal integer value into a TextWriter.
    let intLiteralDecl name isPublic (value : int) (writer : #TextWriter) =
        // Preconditions
        if System.String.IsNullOrWhiteSpace name then
            invalidArg "name" "The variable name cannot be null/empty/whitespace."

        if isPublic then
            sprintf "let [<Literal>] %s = %i" name value
        else
            sprintf "let [<Literal>] private %s = %i" name value
        |> writer.WriteLine

    /// Emits code which creates an array of UInt16 constants into a TextWriter.
    let oneLineArrayUInt16 name isPublic (array : uint16[]) (writer : #TextWriter) =
        // Preconditions
        if System.String.IsNullOrWhiteSpace name then
            invalidArg "name" "The variable name cannot be null/empty/whitespace."

        // Emit the 'let' binding and opening bracket of the array.
        if isPublic then
            sprintf "let %s = [| " name
        else
            sprintf "let private %s = [| " name
        |> writer.Write

        // Emit the array values.
        array
        |> Array.iter (fun x ->
            writer.Write (x.ToString() + "us; "))

        // Emit the closing bracket of the array.
        writer.WriteLine "|]"


/// Miscellaneous helper functions.
[<AutoOpen>]
module private Utils =
    /// Creates a Map whose keys are the values of the given Map.
    /// The value associated with each key is None.
    let valueMap (map : Map<'Key, 'T>) : Map<'T, 'U option> =
        (Map.empty, map)
        ||> Map.fold (fun valueMap _ value ->
            Map.add value None valueMap)

    /// "Flattens" an array of tuples into an array of values.
    let flattenTupleArray (array : ('T * 'T)[]) =
        let len = Array.length array
        let flattened = Array.zeroCreate <| 2 * len
        for i = 0 to len - 1 do
            let a, b = array.[i]
            let idx = 2 * i
            flattened.[idx] <- a
            flattened.[idx + 1] <- b
        flattened

    /// Compute the number of consecutive space characters starting at the beginning of a string.
    /// If the string is empty or contains only space characters, this function returns None.
    let countLeadingSpaces str =
        let mutable index = 0
        let mutable foundNonSpace = false
        let len = String.length str
        while index < len && not foundNonSpace do
            // Is the current character a space character?
            if str.[index] = ' ' then
                index <- index + 1
            else
                foundNonSpace <- true

        // If all of the characters in the string are space characters,
        // return None. Note this also correctly handles empty strings.
        if index = len then
            None
        else
            Some <| uint32 index

    /// Replaces the tab characters in a string with some equivalent tab string.
    let inline replaceTabs tabString (str : string) =
        str.Replace ("\t", tabString)


/// Values used in the ACTION tables created by fsyacc.
[<System.Flags>]
type private ActionValue =
    | Shift = 0x0000us
    | Reduce = 0x4000us
    | Error = 0x8000us
    | Accept = 0xc000us
    | ActionMask = 0xc000us
    | Any = 0xffffus

/// Emit table-driven code which is compatible with the code generated
/// by the older 'fsyacc' tool from the F# PowerPack.
[<RequireQualifiedAccess>]
module private FsYacc =
    open System
    open System.Diagnostics
    open Printf
    open Graham
    open Graham.LR
    open BackendUtils.CodeGen


    //
    let [<Literal>] private defaultLexingNamespace = "Microsoft.FSharp.Text.Lexing"
    //
    let [<Literal>] private defaultParsingNamespace = "Microsoft.FSharp.Text.Parsing"
    /// The namespace where the OCaml-compatible parsers can be found.
    let [<Literal>] private ocamlParsingNamespace = "FSharp.Compatibility.OCaml.Parsing"

    /// The name of the end-of-input terminal.
    let [<Literal>] private endOfInputTerminal : TerminalIdentifier = "end_of_input"
    /// The name of the error terminal.
    let [<Literal>] private errorTerminal : TerminalIdentifier = "error"

    

    /// Emits F# code declaring terminal (token) and nonterminal types
    /// used by the generated parser into an IndentedTextWriter.
    let private parserTypes (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
        (taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>)
        symbolicTokenNames symbolicNonterminalNames tokenTags productionIndices (writer : IndentedTextWriter) =
        (* TODO :   Modify the code below to use taggedGrammar instead of 'tokenTags' and 'productionIndices'.
                    Then, those parameters can be removed. *)

        // Emit the token type declaration.
        quickSummary writer "This type is the type of tokens accepted by the parser."
        unionTypeDecl "token" true processedSpec.Terminals writer
        writer.WriteLine ()

        // Emit the symbolic token-name type declaration.
        quickSummary writer "This type is used to give symbolic names to token indexes, useful for error messages."
        unionTypeDecl "tokenId" false (valueMap symbolicTokenNames) writer
        writer.WriteLine ()

        // Emit the symbolic nonterminal type declaration.
        quickSummary writer "This type is used to give symbolic names to token indexes, useful for error messages."
        do
            /// The symbolic nonterminals. All values in this map are None
            /// since the cases don't carry values.
            let symbolicNonterminals =
                let symbolicNonterminals = valueMap symbolicNonterminalNames
                // Add cases for the starting symbols.
                (symbolicNonterminals, processedSpec.StartSymbols)
                ||> Set.fold (fun symbolicNonterminals startSymbol ->
                    Map.add ("NONTERM__start" + startSymbol) None symbolicNonterminals)

                // Write the type declaration.
            unionTypeDecl "nonterminalId" false symbolicNonterminals writer
        writer.WriteLine ()
         
        // Emit the token -> token-tag function.
        quickSummary writer "Maps tokens to integer indexes."
        writer.WriteLine "let private tagOfToken = function"
        IndentedTextWriter.indented writer <| fun writer ->
            // Emit a case for each terminal (token).
            processedSpec.Terminals
            |> Map.iter (fun tokenName tokenType ->
                let tagValue = Map.find tokenName tokenTags
                match tokenType with
                | None ->
                    sprintf "| %s -> %i" tokenName tagValue
                | Some _ ->
                    sprintf "| %s _ -> %i" tokenName tagValue
                |> writer.WriteLine)
        writer.WriteLine ()

        // Emit the token-tag -> symbolic-token-name function.
        quickSummary writer "Maps integer indices to symbolic token ids."
        writer.WriteLine "let private tokenTagToTokenId = function"
        IndentedTextWriter.indented writer <| fun writer ->
            // Emit a case for each terminal (token).
            tokenTags
            |> Map.iter (fun tokenName tagValue ->
                Map.find tokenName symbolicTokenNames
                |> sprintf "| %i -> %s" tagValue
                |> writer.WriteLine)

            // Emit a catch-all case to handle invalid values.
            let catchAllVariableName = "tokenIdx"
            writer.WriteLine ("| " + catchAllVariableName + " ->")
            IndentedTextWriter.indented writer <| fun writer ->
                // When the catch-all is matched, it should raise an exception.
                writer.WriteLine (
                    "failwithf \"tokenTagToTokenId: Invalid token. (Tag = %i)\" " + catchAllVariableName)
        writer.WriteLine ()

        // Emit the production-index -> symbolic-nonterminal-name function.
        quickSummary writer "Maps production indexes returned in syntax errors to strings representing
                             the non-terminal that would be produced by that production."
        writer.WriteLine "let private prodIdxToNonTerminal = function"
        IndentedTextWriter.indented writer <| fun writer ->
            // Emit cases based on the production-index -> symbolic-nonterminal-name map.
            productionIndices
            |> IntMap.iter (fun productionIndex nonterminalSymbolicName ->
                sprintf "| %i -> %s" productionIndex nonterminalSymbolicName
                |> writer.WriteLine)

            // Emit a catch-all case to handle invalid values.
            let catchAllVariableName = "prodIdx"
            writer.WriteLine ("| " + catchAllVariableName + " ->")
            IndentedTextWriter.indented writer <| fun writer ->
                // When the catch-all is matched, it should raise an exception.
                writer.WriteLine (
                    "failwithf \"prodIdxToNonTerminal: Invalid production index. (Index = %i)\" " + catchAllVariableName)
        writer.WriteLine ()

        // Emit constants for "end-of-input" and "tag of error terminal"
        intLiteralDecl "_fsyacc_endOfInputTag" false
            (Map.find endOfInputTerminal tokenTags) writer
        intLiteralDecl "_fsyacc_tagOfErrorTerminal" false
            (Map.find errorTerminal tokenTags) writer
        writer.WriteLine ()

        // Emit the token -> token-name function.
        quickSummary writer "Gets the name of a token as a string."
        writer.WriteLine "let token_to_string = function"
        IndentedTextWriter.indented writer <| fun writer ->
            // Emit a case for each terminal (token).
            processedSpec.Terminals
            |> Map.iter (fun tokenName tokenType ->
                match tokenType with
                | None ->
                    sprintf "| %s -> \"%s\"" tokenName tokenName
                | Some _ ->
                    sprintf "| %s _ -> \"%s\"" tokenName tokenName
                |> writer.WriteLine)
        writer.WriteLine ()

        // Emit the function for getting the token data.
        quickSummary writer "Gets the data carried by a token as an object."
        writer.WriteLine "let private _fsyacc_dataOfToken = function"
        IndentedTextWriter.indented writer <| fun writer ->
            // Emit a case for each terminal (token).
            processedSpec.Terminals
            |> Map.iter (fun tokenName tokenType ->
                match tokenType with
                | None ->
                    sprintf "| %s -> (null : System.Object)" tokenName
                | Some _ ->
                    sprintf "| %s _fsyacc_x -> box _fsyacc_x" tokenName
                |> writer.WriteLine)
        writer.WriteLine ()

    /// Converts a Graham.LR.LrParserAction into an ActionValue value (used by fsyacc).
    let private actionValue = function
        | Accept ->
            ActionValue.Accept
        | Reduce productionRuleId ->
            ActionValue.Reduce |||
            EnumOfValue (Checked.uint16 productionRuleId)
        | Shift targetStateId ->
            ActionValue.Shift |||
            EnumOfValue (Checked.uint16 targetStateId)

    (* TODO :   Refactor the 'parserTables' function.
                The code which handles each table (or pair of tables, for sparse tables) can be
                moved into a separate function. Once that's done (and everything still works)
                each of those functions should be refactored further into a pair of functions --
                a "pure" function which computes the tables, and another which calls the
                table-computing function then emits code to create the tables into an IndentedTextWriter. *)

    /// Functions for computing the parser tables and emitting them into the generated code.
    [<RequireQualifiedAccess>]
    module internal ParserTables =
        (* TODO :   Modify the functions below to use 'taggedGrammar' instead of 'tokenTags' and 'productionIndices'.
                    Once that's done, remove those parameters. *)

        /// Computes the GOTO table for the parser, then emits it as a sparse (compressed)
        /// table into the generated parser code.
        let private emitGotoTable (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
            (taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>)
            (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>)
            augmentedTerminalTags (productionIndices : IntMap<string>) (writer : IndentedTextWriter) =
            // _fsyacc_gotos
            // _fsyacc_sparseGotoTableRowOffsets
            let _fsyacc_gotos, _fsyacc_sparseGotoTableRowOffsets =
                /// The source and target states of GOTO transitions over each nonterminal.
                let gotoEdges =
                    (Map.empty, parserTable.GotoTable)
                    ||> Map.fold (fun gotoEdges (source, nonterminal) target ->
                        /// The GOTO edges labeled with this nonterminal.
                        let edges =
                            match Map.tryFind nonterminal gotoEdges with
                            | None ->
                                Set.singleton (source, target)
                            | Some edges ->
                                Set.add (source, target) edges

                        // Update the map with the new set of edges for this nonterminal.
                        Map.add nonterminal edges gotoEdges)

                let startSymbolCount = Set.count processedSpec.StartSymbols
                let gotos =
                    // Initialize to a reasonable size to avoid small re-allocations.
                    ResizeArray (4 * gotoEdges.Count)
                let offsets = Array.zeroCreate (startSymbolCount + gotoEdges.Count)

                // Add entries for the "fake" starting nonterminals.
                for i = 0 to startSymbolCount - 1 do
                    gotos.Add 0us
                    gotos.Add (EnumToValue ActionValue.Any)
                    offsets.[i] <- uint16 (2 * i)

                // Add entries for the rest of the nonterminals.
                (startSymbolCount, gotoEdges)
                ||> Map.fold (fun nonterminalIndex nonterminal edges ->
                    // Store the starting index (in the sparse GOTO table) for this nonterminal.
                    offsets.[nonterminalIndex] <- Checked.uint16 (gotos.Count / 2)

                    // Add the number of edges and the "any" action to the sparse GOTOs table.
                    gotos.Add (uint16 <| Set.count edges)
                    gotos.Add (EnumToValue ActionValue.Any)

                    // Add each of the GOTO edges to the sparse GOTO table.
                    edges
                    |> Set.iter (fun (source, target) ->
                        gotos.Add <| Checked.uint16 source
                        gotos.Add <| Checked.uint16 target)

                    // Update the nonterminal index for the next iteration.
                    nonterminalIndex + 1)
                // Discard the counter
                |> ignore

                // Convert the ResizeArray to an array and return it.
                gotos.ToArray (),
                offsets

            Debug.Assert (
                (let elementCount = Checked.uint16 <| Array.length _fsyacc_gotos in
                    _fsyacc_sparseGotoTableRowOffsets
                    |> Array.forall ((>) elementCount)),
                "One or more of the offsets in '_fsyacc_gotos' \
                 is greater than the length of '_fsyacc_sparseGotoTableRowOffsets'.")

            oneLineArrayUInt16 "_fsyacc_gotos" false _fsyacc_gotos writer
            oneLineArrayUInt16 "_fsyacc_sparseGotoTableRowOffsets" false _fsyacc_sparseGotoTableRowOffsets writer

        //
        let private emitStateToProductionIndicesTable (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
            (taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>)
            (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>)
            augmentedTerminalTags (productionIndices : IntMap<string>) (writer : IndentedTextWriter) =
            (* _fsyacc_stateToProdIdxsTableElements *)
            (* _fsyacc_stateToProdIdxsTableRowOffsets *)
            let _fsyacc_stateToProdIdxsTableElements, _fsyacc_stateToProdIdxsTableRowOffsets =
                let parserStates =
                    TagBimap.toArray parserTable.ParserStates

                let stateToProdIdxsTableElements =
                    // Initialize to a reasonable size to avoid small re-allocations.
                    ResizeArray (4 * parserStates.Length)

                let stateToProdIdxsTableRowOffsets =
                    Array.zeroCreate <| Array.length parserStates

                // Populate the arrays from 'parserStates'.
                parserStates
                |> Array.iteri (fun idx (_, items) ->
                    // Record the starting index (offset) for this state.
                    stateToProdIdxsTableRowOffsets.[idx] <-
                        Checked.uint16 stateToProdIdxsTableElements.Count

                    // Add the number of elements for this state to the 'elements' array.
                    stateToProdIdxsTableElements.Add (Checked.uint16 <| Set.count items)

                    // Store the elements for this state into the 'elements' array.
                    items
                    |> Set.iter (fun item ->
                        item.ProductionRuleIndex
                        |> Checked.uint16
                        |> stateToProdIdxsTableElements.Add))

                // Return the constructed arrays.
                stateToProdIdxsTableElements.ToArray (),
                stateToProdIdxsTableRowOffsets

            Debug.Assert (
                (let elementCount = Checked.uint16 <| Array.length _fsyacc_stateToProdIdxsTableElements in
                    _fsyacc_stateToProdIdxsTableRowOffsets
                    |> Array.forall ((>) elementCount)),
                "One or more of the offsets in '_fsyacc_stateToProdIdxsTableRowOffsets' \
                 is greater than the length of '_fsyacc_stateToProdIdxsTableElements'.")

            oneLineArrayUInt16 "_fsyacc_stateToProdIdxsTableElements" false
                _fsyacc_stateToProdIdxsTableElements writer
            oneLineArrayUInt16 "_fsyacc_stateToProdIdxsTableRowOffsets" false
                _fsyacc_stateToProdIdxsTableRowOffsets writer

        //
        let private emitActionTable (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
            (taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>)
            (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>)
            augmentedTerminalTags (productionIndices : IntMap<string>) (writer : IndentedTextWriter) =
            (* _fsyacc_actionTableElements *)
            (* _fsyacc_actionTableRowOffsets *)
            let _fsyacc_actionTableElements, _fsyacc_actionTableRowOffsets =
                //
                let actionsByState =
                    // OPTIMIZE : Some of the computations below could be merged together to
                    // avoid creating intermediate data structures (and avoid unnecessary calculations).
                    (Map.empty, parserTable.ActionTable)
                    ||> Map.fold (fun parserActionsByState (stateId, terminal) actionSet ->
                        match actionSet with
                        | Conflict _ ->
                            let msg = sprintf "Conflicting actions on terminal %O in state #%i." terminal (int stateId)
                            raise <| exn msg
                        | Action action ->
                            let stateActions =
                                let value = terminal, action
                                match Map.tryFind stateId parserActionsByState with
                                | None ->
                                    [value]
                                | Some stateActions ->
                                    value :: stateActions

                            Map.add stateId stateActions parserActionsByState)

                //
                let terminalsByActionByState =
                    actionsByState
                    |> Map.map (fun _ actions ->
                        (Map.empty, actions)
                        ||> List.fold (fun terminalsByAction (terminal, action) ->
                            let terminals =
                                match Map.tryFind action terminalsByAction with
                                | None ->
                                    Set.singleton terminal
                                | Some terminals ->
                                    Set.add terminal terminals

                            Map.add action terminals terminalsByAction))
(*
                /// The total number of parser actions (excluding implicit error actions) for each parser state.
                let actionCountByState =
                    actionsByState
                    |> Map.map (fun _ actions ->
                        List.length actions)
*)
                /// The most-frequent parser action (if any) for each parser state.
                let mostFrequentAction =
                    terminalsByActionByState
                    |> Map.map (fun _ terminalsByAction ->
                        (None, terminalsByAction)
                        ||> Map.fold (fun mostFrequent action terminals ->
                            let terminalCount = Set.count terminals
                            match mostFrequent with
                            | None ->
                                Some (action, terminalCount)
                            | Some (_, mostFrequentActionTerminalCount) ->
                                if terminalCount > mostFrequentActionTerminalCount then
                                    Some (action, terminalCount)
                                else
                                    mostFrequent)
                        |> Option.map fst
                        |> Option.get)

                //
                let compressedActionTable =
                    /// The set of all terminals in the augmented grammar (including the fsyacc error terminal).
                    let allTerminals =
                        (Set.empty, processedSpec.Terminals)
                        ||> Map.fold (fun otherActionTerminals terminal _ ->
                            Set.add (AugmentedTerminal.Terminal terminal) otherActionTerminals)
                        // Add the error and end-of-input terminals.
                        |> Set.add (AugmentedTerminal.Terminal errorTerminal)
                        |> Set.add EndOfFile

                    mostFrequentAction
                    |> Map.map (fun stateId mostFrequentAction ->
                        /// The terminals for which each action is executed in this state.
                        let terminalsByAction =
                            Map.find stateId terminalsByActionByState

                        /// The terminals for which the most-frequent action is taken in this parser state.
                        let mostFrequentActionTerminals =
                            Map.find mostFrequentAction terminalsByAction
                            |> Set.map (fun terminalIndex ->
                                TagBimap.find terminalIndex taggedGrammar.Terminals)
(*
                        /// The total number of parser actions for this state, excluding implicit error actions.
                        let totalActionCount = Map.find stateId actionsByState
*)
                        /// The terminals for which the most-frequent action is NOT taken.
                        let otherActionTerminals =
                            Set.difference allTerminals mostFrequentActionTerminals

                        // We only bother "factoring" out the most-frequent action when doing so actually saves space;
                        // i.e., when the most-frequent action covers a greater number of terminals than the implicit error action.
                        let explicitActionCount =
                            allTerminals
                            |> Set.filter (fun terminal ->
                                // Implicit terminals, such as "error", aren't included here.
                                match TagBimap.tryFindValue terminal taggedGrammar.Terminals with
                                | None -> false
                                | Some terminalIndex ->
                                    Map.containsKey (stateId, terminalIndex) parserTable.ActionTable)
                            |> Set.count

                        let mostFrequentActionValue, entries =
                            let errorActionCount = (Set.count allTerminals) - explicitActionCount
                            if Set.count mostFrequentActionTerminals <= errorActionCount then
                                // No space savings, leave the error action.
                                EnumToValue ActionValue.Error,
                                Map.find stateId actionsByState
                                |> List.toArray
                                |> Array.map (fun (terminalIndex, action) ->
                                    let terminalTag =
                                        let terminal = TagBimap.find terminalIndex taggedGrammar.Terminals
                                        Map.find terminal augmentedTerminalTags
                                    let action = EnumToValue (actionValue action)
                                    (Checked.uint16 terminalTag), action)
                                |> Array.sortWith (fun (tag1, _) (tag2, _) ->
                                    compare tag1 tag2)
                            else
                                EnumToValue (actionValue mostFrequentAction),
                                otherActionTerminals
                                |> Set.toArray
                                |> Array.map (fun terminal ->
                                    let terminalTag = Map.find terminal augmentedTerminalTags
                                    let action =
                                        match TagBimap.tryFindValue terminal taggedGrammar.Terminals with
                                        | None ->
                                            ActionValue.Error
                                        | Some terminalIndex ->
                                            match Map.tryFind (stateId, terminalIndex) parserTable.ActionTable with
                                            | None ->
                                                ActionValue.Error
                                            | Some (Action action) ->
                                                actionValue action
                                            | Some (Conflict _) ->
                                                failwithf "Conflicting actions on terminal %O in state #%i." terminal (int stateId)
                                    (Checked.uint16 terminalTag), (EnumToValue action))
                                |> Array.sortWith (fun (tag1, _) (tag2, _) ->
                                    compare tag1 tag2)

                        // The entries for this state.
                        Array.append [|
                            Checked.uint16 <| Array.length entries;
                            mostFrequentActionValue; |]
                            (flattenTupleArray entries))

                let actionTableElements =
                    // Initialize to roughly the correct size (to avoid multiple small reallocations).
                    ResizeArray (6 * compressedActionTable.Count)

                let actionTableRowOffsets = Array.zeroCreate <| Map.count compressedActionTable

                compressedActionTable
                |> Map.iter (fun stateId elements ->
                    actionTableRowOffsets.[int stateId] <- Checked.uint16 <| actionTableElements.Count / 2
                    actionTableElements.AddRange elements)

                actionTableElements.ToArray (),
                actionTableRowOffsets

            Debug.Assert (
                (let elementCount = Checked.uint16 <| Array.length _fsyacc_actionTableElements in
                    _fsyacc_actionTableRowOffsets
                    |> Array.forall ((>) elementCount)),
                "One or more of the offsets in '_fsyacc_actionTableRowOffsets' \
                 is greater than the length of '_fsyacc_actionTableElements'.")

            oneLineArrayUInt16 "_fsyacc_actionTableElements" false
                _fsyacc_actionTableElements writer
            oneLineArrayUInt16 "_fsyacc_actionTableRowOffsets" false
                _fsyacc_actionTableRowOffsets writer

        //
        let private emitReductionSymbolCounts (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
            (taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>)
            (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>)
            augmentedTerminalTags (productionIndices : IntMap<string>) (writer : IndentedTextWriter) =
            (* _fsyacc_reductionSymbolCounts *)
            let _fsyacc_reductionSymbolCounts =
                let symbolCounts = ResizeArray (IntMap.count productionIndices)

                // The productions created by the start symbols reduce a single value --
                // the start symbols (nonterminals) themselves.
                for i = 0 to (Set.count processedSpec.StartSymbols) - 1 do
                    symbolCounts.Add 1us

                // Add the number of symbols in each production rule.
                processedSpec.ProductionRules
                |> Map.iter (fun _ rules ->
                    rules |> Array.iter (fun rule ->
                        symbolCounts.Add (uint16 <| Array.length rule.Symbols)))

                // Return the symbol count.
                symbolCounts.ToArray ()

            oneLineArrayUInt16 "_fsyacc_reductionSymbolCounts" false
                _fsyacc_reductionSymbolCounts writer

        //
        let emitProductionToNonterminalTable (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
            (taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>)
            (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>)
            augmentedTerminalTags (productionIndices : IntMap<string>) (writer : IndentedTextWriter) =
            (* _fsyacc_productionToNonTerminalTable *)
            let _fsyacc_productionToNonTerminalTable =
                let productionToNonTerminalTable = Array.zeroCreate <| IntMap.count productionIndices

                // The augmented start symbol will always have nonterminal index 0
                // so we don't actually have to write anything to the array for the
                // elements corresponding to it's production rules (because those
                // elements will already be zeroed-out).

                // Add the nonterminal indices for each production rule.
                ((1, Set.count processedSpec.StartSymbols), processedSpec.ProductionRules)
                ||> Map.fold (fun (nonterminalIndex, prodRuleIndex) _ rules ->
                    /// The number of production rules for this nonterminal.
                    let ruleCount = Array.length rules

                    // Set the next 'ruleCount' elements in the array to this nonterminal's index.
                    for i = 0 to ruleCount - 1 do
                        productionToNonTerminalTable.[prodRuleIndex + i] <-
                            Checked.uint16 nonterminalIndex

                    // Update the counters before the next iteration.
                    nonterminalIndex + 1,
                    prodRuleIndex + ruleCount)
                // Discard the counters.
                |> ignore

                // Return the array.
                productionToNonTerminalTable

            oneLineArrayUInt16 "_fsyacc_productionToNonTerminalTable" false
                _fsyacc_productionToNonTerminalTable writer

        //
        let emitImmediateActions (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
            (taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>)
            (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>)
            augmentedTerminalTags (productionIndices : IntMap<string>) (writer : IndentedTextWriter) =
            (* _fsyacc_immediateActions *)
            let _fsyacc_immediateActions =
                // When a state contains a single item whose parser position ("dot")
                // is at the end of the production rule, a Reduce or Accept will be
                // executed immediately upon entering the state.
                // NOTE : The length of this array should be equal to the number of parser states.
                let immediateActions = Array.zeroCreate <| TagBimap.count parserTable.ParserStates

                /// The tagged-index of the Start nonterminal.
                let startNonterminalIndex = TagBimap.findValue AugmentedNonterminal.Start taggedGrammar.Nonterminals
            
                parserTable.ParserStates
                |> TagBimap.iter (fun parserStateId items ->
                    // Set the array element corresponding to this parser state.
                    immediateActions.[int parserStateId] <-
                        // Does this state contain just one (1) item?
                        if Set.count items <> 1 then
                            // Return the value which indicates this parser state has no immediate action.
                            EnumToValue ActionValue.Any
                        else
                            /// The single item in this parser state.
                            let item = Set.minElement items

                            /// The nonterminal produced by this item's production rule.
                            let itemNonterminalIndex = TagMap.find item.ProductionRuleIndex taggedGrammar.NonterminalOfProduction

                            /// This item's production rule.
                            let itemProduction = TagMap.find item.ProductionRuleIndex taggedGrammar.Productions

                            // Is the parser position at the end of the production rule?
                            // (Or, if it's one of the starting productions -- the next-to-last position).
                            if itemNonterminalIndex = startNonterminalIndex &&
                                int item.Position = (Array.length itemProduction - 1) then
                                // This state should have an immediate Accept action.
                                EnumToValue ActionValue.Accept

                            elif int item.Position = Array.length itemProduction then
                                // Return a value representing a Reduce action with this production rule.
                                Reduce item.ProductionRuleIndex
                                |> actionValue
                                |> EnumToValue

                            else
                                // Return the value which indicates this parser state has no immediate action.
                                EnumToValue ActionValue.Any)

                // Return the constructed array.
                immediateActions

            oneLineArrayUInt16 "_fsyacc_immediateActions" false
                _fsyacc_immediateActions writer

        /// Emits F# code which creates the parser tables into an IndentedTextWriter.
        let computeAndEmit (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
            (taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>)
            (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>)
            augmentedTerminalTags (productionIndices : IntMap<string>) (writer : IndentedTextWriter) =
            (* _fsyacc_action_rows *)
            intLiteralDecl "_fsyacc_action_rows" false
                (TagBimap.count parserTable.ParserStates) writer

            // Emit the GOTO table.
            emitGotoTable processedSpec taggedGrammar parserTable augmentedTerminalTags productionIndices writer
            
            // Emit the state->production-indices table.
            emitStateToProductionIndicesTable processedSpec taggedGrammar parserTable augmentedTerminalTags productionIndices writer

            // Emit the ACTION table.
            emitActionTable processedSpec taggedGrammar parserTable augmentedTerminalTags productionIndices writer
            
            // Emit the reduction symbol counts.
            emitReductionSymbolCounts processedSpec taggedGrammar parserTable augmentedTerminalTags productionIndices writer

            // Emit the production-index->nonterminal table.
            emitProductionToNonterminalTable processedSpec taggedGrammar parserTable augmentedTerminalTags productionIndices writer
            
            // Emit the immediate actions table.
            emitImmediateActions processedSpec taggedGrammar parserTable augmentedTerminalTags productionIndices writer


    /// Emits F# code for a single reduction action into an IndentedTextWriter.
    let private reduction (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
        (taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>) (nonterminal : NonterminalIdentifier)
        (symbols : Symbol<NonterminalIdentifier, TerminalIdentifier>[]) (action : CodeFragment) (options, writer : IndentedTextWriter) : unit =
        // Write the function declaration for this semantic action.
        fprintfn writer "(fun (parseState : %s.IParseState) ->"
            <| defaultArg options.ParserInterpreterNamespace defaultParsingNamespace
        IndentedTextWriter.indented writer <| fun writer ->
        // Emit code to get the values of symbols carrying data values.
        symbols
        |> Array.iteri (fun idx symbol ->
            match symbol with
            | Symbol.Nonterminal nonterminal ->
                match Map.find nonterminal processedSpec.Nonterminals with
                | (Some _) as declaredType ->
                    declaredType
                | None ->
                    // Create a generic type parameter to use for this nonterminal and let
                    // the F# compiler use type inference to figure out what type it should be.
                    Some <| "'" + nonterminal
            | Symbol.Terminal terminal ->
                Map.find terminal processedSpec.Terminals
            // Emit a let-binding to get the value of this symbol if it carries any data.
            |> Option.iter (fun symbolType ->
                fprintfn writer "let _%d = (let data = parseState.GetInput(%d) in (Microsoft.FSharp.Core.Operators.unbox data : %s)) in"
                    (idx + 1) (idx + 1) symbolType))

        /// The type of the value carried by the nonterminal produced by this rule.
        let nonterminalValueType =
            match Map.tryFind nonterminal processedSpec.Nonterminals with
            | Some (Some declaredType) ->
                declaredType
            | None
            | Some None ->
                // Create a generic type parameter to use for this nonterminal and let
                // the F# compiler use type inference to figure out what type it should be.
                "'" + nonterminal

        (*  Split 'action' into multiple lines. Determine the minimum amount of whitespace
            which appears on the left of any line in the action, but do not consider blank
            lines. Then, trim this minimum amount of whitespace from the left side of each
            line. When this is done, the action can be written line-by-line using the standard
            'writer.WriteLine' method of the IndentedTextWriter, and the generated code will
            have the correct indentation. *)

        /// The individual lines of the reduction action code, trimmed to remove a number of
        /// leading spaces common to all non-empty/non-whitespace lines.
        let trimmedActionLines =
            /// The individual lines of the reduction action code,
            /// annotated with the number of leading spaces on that line.
            // OPTIMIZE : Use functions from ExtCore.String.Split here to avoid creating unnecessary strings.
            let annotatedActionLines =
                action.Split ([| "\r\n"; "\n"; "\r" |], StringSplitOptions.None)
                |> Array.map (fun line ->
                    // First replace any tab characters in the string.
                    let line = replaceTabs "    " line
                    let leadingSpaces = countLeadingSpaces line
                    line, leadingSpaces)
        
            /// The minimum number of spaces on the left side of any line of code.
            let minIndentation =
                let minIndentation =
                    (None, annotatedActionLines)
                    ||> Array.fold (fun x (_, y) ->
                        match x, y with
                        | None, None ->
                            None
                        | (Some _ as x), None ->
                            x
                        | None, (Some _ as y) ->
                            y
                        | Some x, Some y ->
                            Some <| min x y)

                // Default to zero (0) indentation.
                defaultArg minIndentation GenericZero

            // Remove the same amount of indentation from every non-empty line.
            annotatedActionLines
            |> Array.map (fun (line, leadingSpaces) ->
                match leadingSpaces with
                | None ->
                    assert (String.IsNullOrWhiteSpace line)
                    String.Empty
                | Some _ ->
                    // Remove the computed number of spaces from the left side of this line.
                    line.Substring (int minIndentation))
            
        // Emit the semantic action code, wrapped in a bit of code which boxes the return value.
        writer.WriteLine "Microsoft.FSharp.Core.Operators.box"
        IndentedTextWriter.indented writer <| fun writer ->
            writer.WriteLine "("
            IndentedTextWriter.indented writer <| fun writer ->
                writer.WriteLine "("
                IndentedTextWriter.indented writer <| fun writer ->
                    // Write the trimmed action-code lines to the IndentedTextWriter one-by-one.
                    // This ensures they're indented correctly with respect to the rest of the emitted code.
                    trimmedActionLines
                    |> Array.iter writer.WriteLine
                writer.WriteLine ")"

            // Emit the nonterminal type for this production rule.
            fprintfn writer ": %s))" nonterminalValueType

    /// Replaces the placeholders for symbols in production rules
    /// (e.g., $2) with valid F# value identifiers.
    let inline private replaceSymbolPlaceholders (code : CodeFragment) =
        System.Text.RegularExpressions.Regex.Replace (code, "\$(?=\d+)", "_")

    /// Emits the user-defined semantic actions for the reductions.
    let private reductions (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
        (taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>) (options, writer : IndentedTextWriter) : unit =
        /// The default action to execute when a production rule
        /// has no semantic action code associated with it.
        let defaultAction =
            options.ParserInterpreterNamespace
            |> Option.fill defaultParsingNamespace
            |> sprintf "raise (%s.Accept (Microsoft.FSharp.Core.Operators.box _1))"

        // _fsyacc_reductions
        writer.WriteLine "let private _fsyacc_reductions = [|"
        IndentedTextWriter.indented writer <| fun writer ->
            // Emit actions for the augmented starting nonterminals.
            processedSpec.StartSymbols
            |> Set.iter (fun startSymbol ->
                let startNonterminal = "_start" + startSymbol
                reduction processedSpec taggedGrammar startNonterminal [| Symbol.Nonterminal startSymbol |] defaultAction (options, writer))

            // Emit the actions for each of the production rules.
            processedSpec.ProductionRules
            |> Map.iter (fun nonterminal rules ->
                rules |> Array.iter (fun rule ->
                    let action =
                        // Replace the symbol placeholders; e.g., change $2 to _2
                        rule.Action
                        |> Option.map replaceSymbolPlaceholders
                        |> Option.fill defaultAction

                    reduction processedSpec taggedGrammar nonterminal rule.Symbols action (options, writer)))
            
            // Emit the closing bracket of the array.
            writer.WriteLine "|]"

        // Write a blank line for readability.
        writer.WriteLine ()

    /// Emits F# code which creates the 'tables' record and defines the
    /// parser functions into an IndentedTextWriter.
    let private tablesRecordAndParserFunctions typedStartSymbols terminalCount (options, writer : IndentedTextWriter) =
        /// The namespace where the parser interpreter can be found.
        let parsingNamespace =
            options.ParserInterpreterNamespace
            |> Option.fill defaultParsingNamespace

        // Emit the 'tables' record.
        fprintfn writer "let tables () : %s.Tables<_> = {" parsingNamespace
        IndentedTextWriter.indented writer <| fun writer ->
            writer.WriteLine "reductions = _fsyacc_reductions;"
            writer.WriteLine "endOfInputTag = _fsyacc_endOfInputTag;"
            writer.WriteLine "tagOfToken = tagOfToken;"
            writer.WriteLine "dataOfToken = _fsyacc_dataOfToken;"
            writer.WriteLine "actionTableElements = _fsyacc_actionTableElements;"
            writer.WriteLine "actionTableRowOffsets = _fsyacc_actionTableRowOffsets;"
            writer.WriteLine "stateToProdIdxsTableElements = _fsyacc_stateToProdIdxsTableElements;"
            writer.WriteLine "stateToProdIdxsTableRowOffsets = _fsyacc_stateToProdIdxsTableRowOffsets;"
            writer.WriteLine "reductionSymbolCounts = _fsyacc_reductionSymbolCounts;"
            writer.WriteLine "immediateActions = _fsyacc_immediateActions;"
            writer.WriteLine "gotos = _fsyacc_gotos;"
            writer.WriteLine "sparseGotoTableRowOffsets = _fsyacc_sparseGotoTableRowOffsets;"
            writer.WriteLine "tagOfErrorTerminal = _fsyacc_tagOfErrorTerminal;"

            writer.WriteLine "parseError ="
            IndentedTextWriter.indented writer <| fun writer ->
                fprintfn writer "(fun (ctxt : %s.ParseErrorContext<_>) ->" parsingNamespace
                IndentedTextWriter.indented writer <| fun writer ->
                    writer.WriteLine "match parse_error_rich with"
                    writer.WriteLine "| Some f -> f ctxt"
                    writer.WriteLine "| None -> parse_error ctxt.Message);"

            fprintfn writer "numTerminals = %i;" terminalCount
            writer.WriteLine "productionToNonTerminalTable = _fsyacc_productionToNonTerminalTable;"

            // Write the closing bracket for the record,
            // and an additional newline for spacing.
            writer.WriteLine "}"
            writer.WriteLine ()

        // Emit the parser "engine" function.
        writer.WriteLine "let engine lexer lexbuf startState ="
        IndentedTextWriter.indented writer <| fun writer ->
            writer.WriteLine "(tables ()).Interpret(lexer, lexbuf, startState)"
        writer.WriteLine ()

        // Emit a parser function for each of the start symbols.
        typedStartSymbols
        |> Map.iter (fun startSymbol startSymbolType ->
            fprintfn writer "let %s lexer lexbuf : %s =" startSymbol startSymbolType
            IndentedTextWriter.indented writer <| fun writer ->
                writer.WriteLine "unbox ((tables ()).Interpret(lexer, lexbuf, 0))"
            writer.WriteLine ())

    /// Emits code for an fsyacc-compatible parser into an IndentedTextWriter.
    let emit (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
        (taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>)
        (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>)
        (options : FsyaccBackendOptions, writer : IndentedTextWriter) : unit =
        (* Emit the module declaration. *)
        do
            quickSummary writer "Implementation file for parser generated by the fsyacc-compatibility backend for fsharpyacc."

            /// The name of the emitted parser module.
            let parserModuleName =
                defaultArg options.ModuleName "Parser"
        
            if options.InternalModule then
                fprintfn writer "module internal %s" parserModuleName
            else
                fprintfn writer "module %s" parserModuleName
            writer.WriteLine ()

        // Emit a "nowarn" directive to disable a certain type-related warning message.
        fprintf writer "#nowarn \"%i\" " 64
        comment writer "turn off warnings that type variables used in production annotations are instantiated to concrete type"
        writer.WriteLine ()

        (* Emit the default "open" declarations. *)
        [|  defaultLexingNamespace;
            defaultParsingNamespace + ".ParseHelpers"; |]
        |> Array.iter (fprintfn writer "open %s")
        writer.WriteLine ()

        (* Emit additional "open" declarations, if any. *)
        if not <| Array.isEmpty options.OpenDeclarations then
            Array.iter (fprintfn writer "open %s") options.OpenDeclarations
            writer.WriteLine ()

        (* Emit the header code. *)
        processedSpec.Header
        |> Option.iter (fun header ->
            // Write the header code into the TextWriter.
            // We split the code into individual lines, then write them one at a time to the
            // IndentedTextWriter; this ensures that the newlines are correct for this system
            // and also that the indentation level is correct.
            // OPTIMIZE : Use String.Split.iter from ExtCore.
            header.Split ([| "\r\n"; "\r"; "\n" |], StringSplitOptions.None)
            |> Array.iter (fun codeLine ->
                // TODO : Trim the lines? We'd have to process the entire array first
                // to determine the "base" indentation level, then trim only that much
                // from the front of each string.
                writer.WriteLine codeLine)

            writer.WriteLine ())

        do
            (* TODO :   The 'tokenTags' and 'productionIndices' variables can be removed once
                        the 'parserTypes' and 'parserTables' functions have been modified to
                        get the information they need from 'taggedGrammar'. *)
            /// Maps terminals (tokens) to symbolic token names.
            let symbolicTerminalNames =
                processedSpec.Terminals
                // Add the end-of-input and error terminals to the map.
                |> Map.add endOfInputTerminal None
                |> Map.add errorTerminal None
                |> Map.map (fun terminalName _ ->
                    "TOKEN_" + terminalName)

            /// Maps nonterminal identifiers to symbolic nonterminal names.
            let symbolicNonterminalNames =
                processedSpec.Nonterminals
                |> Map.map (fun nonterminalName _ ->
                    "NONTERM_" + nonterminalName)

            /// Integer indices (tags) of terminals (tokens).
            let terminalTags =
                ((Map.empty, 0), processedSpec.Terminals)
                ||> Map.fold (fun (tokenTags, index) terminal _ ->
                    Map.add terminal index tokenTags,
                    index + 1)
                // Add the end-of-input and error terminals and discard the index value.
                |> fun (tokenTags, index) ->
                    tokenTags
                    |> Map.add errorTerminal index
                    |> Map.add endOfInputTerminal (index + 1)

            /// Maps production indices to the symbolic name of the nonterminal produced by each production rule.
            let productionIndices : IntMap<string> =
                let productionIndices_productionIndex =
                    ((IntMap.empty, 0), processedSpec.StartSymbols)
                    ||> Set.fold (fun (productionIndices, productionIndex) startSymbol ->
                        /// The symbolic name of the nonterminal produced by this start symbol.
                        let nonterminalName = "NONTERM__start" + startSymbol
                    
                        // Increment the production index for the next iteration.
                        IntMap.add productionIndex nonterminalName productionIndices,
                        productionIndex + 1)

                // Add the production rules.
                (productionIndices_productionIndex, processedSpec.ProductionRules)
                ||> Map.fold (fun productionIndices_productionIndex nonterminal rules ->
                    /// The symbolic name of this nonterminal.
                    let nonterminalSymbolicName = Map.find nonterminal symbolicNonterminalNames

                    // OPTIMIZE : There's no need to fold over the array of rules, since the
                    // only thing that matters is the _number_ of rules.
                    // Replace this with a call to Range.fold.
                    (productionIndices_productionIndex, rules)
                    ||> Array.fold (fun (productionIndices, productionIndex) _ ->
                        IntMap.add productionIndex nonterminalSymbolicName productionIndices,
                        productionIndex + 1))
                // Discard the production index counter.
                |> fst

            // Emit the parser types (e.g., the token type).
            parserTypes processedSpec taggedGrammar symbolicTerminalNames symbolicNonterminalNames terminalTags productionIndices writer

            do
                /// Integer indices (tags) of the augmented terminals (tokens).
                let augmentedTerminalTags =
                    ((Map.empty, 0), processedSpec.Terminals)
                    ||> Map.fold (fun (tokenTags, index) terminal _ ->
                        Map.add (AugmentedTerminal.Terminal terminal) index tokenTags,
                        index + 1)
                    // Add the end-of-input and error terminals and discard the index value.
                    |> fun (tokenTags, index) ->
                        tokenTags
                        |> Map.add (AugmentedTerminal.Terminal errorTerminal) index
                        |> Map.add EndOfFile (index + 1)

                // Emit the parser tables.
                ParserTables.computeAndEmit processedSpec taggedGrammar parserTable augmentedTerminalTags productionIndices writer

            // Emit the reduction functions (i.e., the user-specified actions / code fragments).
            reductions processedSpec taggedGrammar (options, writer)

        do
            // Emit the parser "tables" record and parser functions.
            let terminalCount =
                // TEMP : Add 2 to account for the end-of-input and error tokens.
                processedSpec.Terminals.Count + 2

            let typedStartSymbols =
                (Map.empty, processedSpec.StartSymbols)
                ||> Set.fold (fun typedStartSymbols startSymbol ->
                    let startSymbolType =
                        Map.find startSymbol processedSpec.Nonterminals
                        // Start symbols are required to have a type, so if this breaks
                        // the problem is in the validation stage of the compiler.
                        |> Option.get

                    Map.add startSymbol startSymbolType typedStartSymbols)

            tablesRecordAndParserFunctions typedStartSymbols terminalCount (options, writer)

        // Flush the writer before returning, to force it to write any
        // output text remaining in it's internal buffer.
        writer.Flush ()


/// A backend which emits code implementing a table-based pattern matcher
/// compatible with 'fsyacc' and the table interpreters in the F# PowerPack.
[<Export(typeof<IBackend>)>]
type FsYaccBackend () =
    interface IBackend with
        member this.Invoke (processedSpec, taggedGrammar, parserTable, options) : unit =
            /// Compilation options specific to this backend.
            let fsyaccOptions =
                match options.FsyaccBackendOptions with
                | None ->
                    raise <| exn "No backend-specific options were provided."
                | Some options ->
                    options

            // Generate the code and write it to the specified file.
            using (File.CreateText fsyaccOptions.OutputPath) <| fun streamWriter ->
                use indentedTextWriter =
                    // Set the indentation to the standard F# indent (4 spaces).
                    new IndentedTextWriter (streamWriter, "    ")

                FsYacc.emit processedSpec taggedGrammar parserTable (fsyaccOptions, indentedTextWriter)

