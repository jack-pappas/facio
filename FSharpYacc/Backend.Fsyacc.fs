(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

namespace FSharpYacc.Plugin

open System.ComponentModel.Composition
open System.IO
//open System.Text
open LanguagePrimitives
open FSharpYacc
open FSharpYacc.Ast
open FSharpYacc.Compiler


/// Emit table-driven code which is compatible with the code generated
/// by the older 'fsyacc' tool from the F# PowerPack.
[<RequireQualifiedAccess>]
module private FsYacc =
    open System
    open System.CodeDom.Compiler
    open Graham.Grammar
    open Graham.LR
    open BackendUtils.CodeGen

    //
    let [<Literal>] private defaultLexingNamespace = "Microsoft.FSharp.Text.Lexing"
    //
    let [<Literal>] private defaultParsingNamespace = "Microsoft.FSharp.Text.Parsing"
    /// The namespace where the OCaml-compatible parsers can be found.
    let [<Literal>] private ocamlParsingNamespace = "Microsoft.FSharp.Compatibility.OCaml.Parsing"

    /// Values used in the ACTION tables created by fsyacc.
    [<Flags>]
    type private ActionValue =
        | Shift = 0x0000us
        | Reduce = 0x4000us
        | Error = 0x8000us
        | Accept = 0xc000us
        | ActionMask = 0xc000us
        | Any = 0xffffus

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

    /// Emit a formatted string as a single-line F# comment into an IndentedTextWriter.
    let inline private comment (writer : IndentedTextWriter) fmt : ^T =
        writer.Write "// "
        Printf.fprintfn writer fmt

    /// Emits a formatted string as a quick-summary (F# triple-slash comment) into an IndentedTextWriter.
    let inline private quickSummary (writer : IndentedTextWriter) fmt : ^T =
        fmt |> Printf.ksprintf (fun str ->
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
    let private unionTypeDecl (typeName : string, isPublic, cases : Map<string, string option>) (writer : IndentedTextWriter) =
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
    let private intLiteralDecl (name, isPublic, value : int) (writer : #TextWriter) =
        // Preconditions
        if System.String.IsNullOrWhiteSpace name then
            invalidArg "name" "The variable name cannot be null/empty/whitespace."

        if isPublic then
            sprintf "let [<Literal>] %s = %i" name value
        else
            sprintf "let [<Literal>] private %s = %i" name value
        |> writer.WriteLine

    /// Emits code which creates an array of UInt16 constants into a TextWriter.
    let private oneLineArrayUInt16 (name, isPublic, array : uint16[]) (writer : #TextWriter) =
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

    /// Creates a Map whose keys are the values of the given Map.
    /// The value associated with each key is None.
    let private valueMap (map : Map<'Key, 'T>) : Map<'T, 'U option> =
        (Map.empty, map)
        ||> Map.fold (fun valueMap _ value ->
            Map.add value None valueMap)

    /// The name of the end-of-input terminal.
    let [<Literal>] private endOfInputTerminal : TerminalIdentifier = "end_of_input"
    /// The name of the error terminal.
    let [<Literal>] private errorTerminal : TerminalIdentifier = "error"

    /// Emits code for an fsyacc-compatible parser into an IndentedTextWriter.
    let emit (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>,
                parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>) (writer : IndentedTextWriter) : unit =
        // TODO : Emit the module declaration
        //

        // TODO : Emit the "open" statements
        //

        // TODO : Emit the header code
        //

        // Emit the token type declaration.
        comment writer "This type is the type of tokens accepted by the parser"
        unionTypeDecl ("token", true, processedSpec.Terminals) writer
        writer.WriteLine ()

        /// Maps terminals (tokens) to symbolic token names.
        let symbolicTokenNames =
            processedSpec.Terminals
            // Add the end-of-input and error terminals to the map.
            |> Map.add endOfInputTerminal None
            |> Map.add errorTerminal None
            |> Map.map (fun terminalName _ ->
                "TOKEN_" + terminalName)

        // Emit the symbolic token-name type declaration.
        quickSummary writer "This type is used to give symbolic names to token indexes, useful for error messages."
        unionTypeDecl ("tokenId", false, valueMap symbolicTokenNames) writer
        writer.WriteLine ()

        /// Maps nonterminal identifiers to symbolic nonterminal names.
        let symbolicNonterminalNames =
            processedSpec.Nonterminals
            |> Map.map (fun nonterminalName _ ->
                "NONTERM_" + nonterminalName)

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
            unionTypeDecl ("nonterminalId", false, symbolicNonterminals) writer
        writer.WriteLine ()

        /// Integer indices (tags) of terminals (tokens).
        let tokenTags =
            ((Map.empty, 0), processedSpec.Terminals)
            ||> Map.fold (fun (tokenTags, index) terminal _ ->
                Map.add terminal index tokenTags,
                index + 1)
            // Add the end-of-input and error terminals and discard the index value.
            |> fun (tokenTags, index) ->
                tokenTags
                |> Map.add errorTerminal index
                |> Map.add endOfInputTerminal (index + 1)
         
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

        /// Maps production indices to the symbolic name of the nonterminal produced by each production rule.
        let productionIndices =
            let productionIndices_productionIndex =
                ((Map.empty, 0), processedSpec.StartSymbols)
                ||> Set.fold (fun (productionIndices, productionIndex) startSymbol ->
                    /// The symbolic name of the nonterminal produced by this start symbol.
                    let nonterminalName = "NONTERM__start" + startSymbol
                    
                    // Increment the production index for the next iteration.
                    Map.add productionIndex nonterminalName productionIndices,
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
                    Map.add productionIndex nonterminalSymbolicName productionIndices,
                    productionIndex + 1))
            // Discard the production index counter.
            |> fst

        // Emit the production-index -> symbolic-nonterminal-name function.
        quickSummary writer "Maps production indexes returned in syntax errors to strings representing
                             the non-terminal that would be produced by that production."
        writer.WriteLine "let private prodIdxToNonTerminal = function"
        IndentedTextWriter.indented writer <| fun writer ->
            // Emit cases based on the production-index -> symbolic-nonterminal-name map.
            productionIndices
            |> Map.iter (fun productionIndex nonterminalSymbolicName ->
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
        intLiteralDecl ("_fsyacc_endOfInputTag", false,
            Map.find endOfInputTerminal tokenTags) writer
        intLiteralDecl ("_fsyacc_tagOfErrorTerminal", false,
            Map.find errorTerminal tokenTags) writer
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


        (*** Emit parser tables ***)

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

        // _fsyacc_gotos
        // _fsyacc_sparseGotoTableRowOffsets
        let _fsyacc_gotos, _fsyacc_sparseGotoTableRowOffsets =
            let startSymbolCount = Set.count processedSpec.StartSymbols
            let gotos = ResizeArray ()
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
                offsets.[nonterminalIndex] <- Checked.uint16 gotos.Count

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

        oneLineArrayUInt16 ("_fsyacc_gotos", false,
            _fsyacc_gotos) writer
        oneLineArrayUInt16 ("_fsyacc_sparseGotoTableRowOffsets", false,
            _fsyacc_sparseGotoTableRowOffsets) writer


        (* _fsyacc_stateToProdIdxsTableElements *)
        let _fsyacc_stateToProdIdxsTableElements =
            [| |]

        oneLineArrayUInt16 ("_fsyacc_stateToProdIdxsTableElements", false,
            _fsyacc_stateToProdIdxsTableElements) writer


        (* _fsyacc_stateToProdIdxsTableRowOffsets *)
        let _fsyacc_stateToProdIdxsTableRowOffsets =
            [| |]

        oneLineArrayUInt16 ("_fsyacc_stateToProdIdxsTableRowOffsets", false,
            _fsyacc_stateToProdIdxsTableRowOffsets) writer


        (* _fsyacc_action_rows *)
        intLiteralDecl ("_fsyacc_action_rows", false,
            parserTable.ParserStates.Count) writer


        (* _fsyacc_actionTableElements *)
        let _fsyacc_actionTableElements =
            [| |]

        oneLineArrayUInt16 ("_fsyacc_actionTableElements", false,
            _fsyacc_actionTableElements) writer


        (* _fsyacc_actionTableRowOffsets *)
        let _fsyacc_actionTableRowOffsets =
            [| |]

        oneLineArrayUInt16 ("_fsyacc_actionTableRowOffsets", false,
            _fsyacc_actionTableRowOffsets) writer


        (* _fsyacc_reductionSymbolCounts *)
        let _fsyacc_reductionSymbolCounts =
            let symbolCounts = ResizeArray (productionIndices.Count)

            // The productions created by the start symbols reduce a single value --
            // the start symbols (nonterminals) themselves.
            for i = 0 to (Set.count processedSpec.StartSymbols) - 1 do
                symbolCounts.Add 1us

            // Add the number of symbols in each production rule.
            processedSpec.ProductionRules
            |> Map.iter (fun _ rules ->
                rules |> Array.iter (Array.length >> uint16 >> symbolCounts.Add))

            // Return the symbol count.
            symbolCounts.ToArray ()

        oneLineArrayUInt16 ("_fsyacc_reductionSymbolCounts", false,
            _fsyacc_reductionSymbolCounts) writer

        (* _fsyacc_productionToNonTerminalTable *)
        let _fsyacc_productionToNonTerminalTable =
            let productionToNonTerminalTable = Array.zeroCreate productionIndices.Count

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
                        uint16 nonterminalIndex

                // Update the counters before the next iteration.
                nonterminalIndex + 1,
                prodRuleIndex + ruleCount)
            // Discard the counters.
            |> ignore

            // Return the array.
            productionToNonTerminalTable

        oneLineArrayUInt16 ("_fsyacc_productionToNonTerminalTable", false,
            _fsyacc_productionToNonTerminalTable) writer


        (* _fsyacc_immediateActions *)
        let _fsyacc_immediateActions =
            // When a state contains a single item whose parser position ("dot")
            // is at the end of the production rule, a Reduce or Accept will be
            // executed immediately upon entering the state.
            // NOTE : The length of this array should be equal to the number of parser states.
            let immediateActions = Array.zeroCreate parserTable.ParserStates.Count

            // TEMP : Remove this once we rewrite the rest of this code to work with
            // an augmented grammar instead of the "raw" grammar.
            let productionRuleIndices =
                let startSymbolCount = Set.count processedSpec.StartSymbols
                ((Map.empty, startSymbolCount), processedSpec.ProductionRules)
                ||> Map.fold (fun productionIndices_productionIndex nonterminal rules ->
                    (productionIndices_productionIndex, rules)
                    ||> Array.fold (fun (productionIndices, productionIndex) symbols ->
                        Map.add (nonterminal, symbols) productionIndex productionIndices,
                        productionIndex + 1))
                // Discard the production index counter.
                |> fst

            parserTable.ParserStates
            |> Map.iter (fun parserStateId items ->
                // Set the array element corresponding to this parser state.
                immediateActions.[int parserStateId - 1] <-
                    // Does this state contain just one (1) item?
                    if Set.count items <> 1 then
                        // Return the value which indicates this parser state has no immediate action.
                        EnumToValue ActionValue.Any
                    else
                        /// The single item in this parser state.
                        let item = Set.minElement items

                        // Is the parser position at the end of the production rule?
                        // (Or, if it's one of the starting productions -- the next-to-last position).
                        match item.Nonterminal with
                        | Start when int item.Position = (Array.length item.Production - 1) ->
                            // This state should have an immediate Accept action.
                            EnumToValue ActionValue.Accept

                        | AugmentedNonterminal.Nonterminal nonterminal
                            when int item.Position = Array.length item.Production ->
                            /// The (augmented) symbols in this production rule.
                            let symbols =
                                item.Production
                                |> Array.map (function
                                    | Nonterminal nonterminal ->
                                        match nonterminal with
                                        | Start ->
                                            failwith "Start symbol in an item which is not part of the start production."
                                        | AugmentedNonterminal.Nonterminal nonterminal ->
                                            Nonterminal nonterminal
                                    | Terminal terminal ->
                                        match terminal with
                                        | EndOfFile ->
                                            failwith "Unexpected end-of-file symbol."
                                        | AugmentedTerminal.Terminal terminal ->
                                            Terminal terminal)

                            // The index of the production rule to reduce by.
                            Map.find (nonterminal, symbols) productionRuleIndices
                            |> Int32WithMeasure
                            // Return a value representing a Reduce action with this production rule.
                            |> Reduce
                            |> actionValue
                            |> EnumToValue

                        | _ ->
                            // Return the value which indicates this parser state has no immediate action.
                            EnumToValue ActionValue.Any)

            // Return the constructed array.
            immediateActions

        oneLineArrayUInt16 ("_fsyacc_immediateActions", false,
            _fsyacc_immediateActions) writer

        // _fsyacc_reductions
        // TODO : When emitting the code, need to replace placeholder values (e.g., $2)
        // with the corresponding variable value (e.g., _2).

        // TODO : Emit the parser "tables" record and parser functions
        //

        // TEMP
        writer.Flush () // Flush before throwing the exception, so we can see the output.
        raise <| System.NotImplementedException "Fsyacc.emit"

/// A backend which emits code implementing a table-based pattern matcher
/// compatible with 'fsyacc' and the table interpreters in the F# PowerPack.
[<Export(typeof<IBackend>)>]
type FsyaccBackend () =
    interface IBackend with
        member this.Invoke (processedSpec, parserTable, options) : unit =
            /// Compilation options specific to this backend.
            let fsyaccOptions =
                match options.FsyaccBackendOptions with
                | None ->
                    raise <| exn "No backend-specific options were provided."
                | Some options ->
                    options

            (* TODO :   This backend places an additional restriction on the parser specification --
                        all start symbols (nonterminals) must produce the same type.
                        For now, we should implement a simple check for this and raise an exception
                        if they have different types; in the future, we should find a way to pass this
                        constraint into the Compiler.precompile function so it can provide a better
                        error message for the user. *)

            // Generate the code and write it to the specified file.
            using (File.CreateText fsyaccOptions.OutputPath) <| fun streamWriter ->
                use indentedTextWriter =
                    new System.CodeDom.Compiler.IndentedTextWriter (streamWriter)
                FsYacc.emit (processedSpec, parserTable) indentedTextWriter

