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

    /// The indentation string used when emitting code.
    let [<Literal>] indent = "    "

    /// Character sequences representing "newline" for various platforms.
    let newlines = [| "\r\n"; "\n"; "\r" |]

    /// Emit a formatted string as a single-line F# comment into an IndentedTextWriter.
    let inline comment (writer : IndentedTextWriter) fmt : ^T =
        writer.Write "// "
        fprintfn writer fmt

    /// Emits a formatted string as a quick-summary (F# triple-slash comment) into an IndentedTextWriter.
    let inline quickSummary (writer : IndentedTextWriter) fmt : ^T =
        fmt |> Printf.ksprintf (fun summaryComment ->
            // Split the string into individual lines, then write the lines
            // to the IndentedTextWriter as triple-slash documentation comments.
            // OPTIMIZE : Use the String.Split.iter and Substring.trim functions from ExtCore.
            summaryComment.Split (newlines, System.StringSplitOptions.None)
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

//
[<AutoOpen>]
module private FsYaccConstants =
    //
    let [<Literal>] defaultLexingNamespace = "Microsoft.FSharp.Text.Lexing"
    //
    let [<Literal>] defaultParsingNamespace = "Microsoft.FSharp.Text.Parsing"
    /// The namespace where the OCaml-compatible parsers can be found.
    let [<Literal>] ocamlParsingNamespace = "FSharp.Compatibility.OCaml.Parsing"

    /// The name of the end-of-input terminal.
    let [<Literal>] endOfInputTerminal : TerminalIdentifier = "end_of_input"
    /// The name of the error terminal.
    let [<Literal>] errorTerminal : TerminalIdentifier = "error"


//
[<RequireQualifiedAccess>]
module internal ParserTypes =
    open Graham
    open BackendUtils.CodeGen


    //
    let private symbolicTerminalName terminal =
        let suffix =
            match terminal with
            | AugmentedTerminal.EndOfFile ->
                endOfInputTerminal
            | AugmentedTerminal.Terminal (terminal : TerminalIdentifier) ->
                terminal

        "TOKEN_" + suffix
                
    //
    let (*private*) symbolicNonterminalName (nonterminal : NonterminalIdentifier) =
        "NONTERM_" + nonterminal

    //
    let (*private*) symbolicStartingNonterminalName (startingNonterminal : NonterminalIdentifier) =
        "NONTERM__start" + startingNonterminal

    /// Emit the token type declaration.
    let private emitTokenTypeDecl
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (writer : IndentedTextWriter) =
        let terminalsAndTypes =
            (Map.empty, taggedGrammar.Terminals)
            ||> TagBimap.fold (fun terminalsAndTypes terminalIndex terminal ->
                // Built-in and implicit terminals are not included in this map.
                match terminal with
                | AugmentedTerminal.EndOfFile ->
                    terminalsAndTypes
                | AugmentedTerminal.Terminal terminal ->
                    // Is this one of the implicit terminals?
                    // TODO : This should check against a set to make things easier...but for now, we only have one implicit terminal.
                    // Perhaps create a 3-way active pattern (|EndOfFile|BuiltIn|Declared|) to take care of it.
                    if terminal = errorTerminal then
                        terminalsAndTypes
                    else
                        let terminalType = TagMap.tryFind terminalIndex taggedGrammar.TerminalTypes
                        Map.add terminal terminalType terminalsAndTypes)

        quickSummary writer "This type is the type of tokens accepted by the parser."
        unionTypeDecl "token" true terminalsAndTypes writer
        writer.WriteLine ()

    // Emit the symbolic token-name type declaration.
    let private emitSymbolicTokenNameTypeDecl
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (writer : IndentedTextWriter) =
        let symbolicTerminalNamesAndTypes =
            (Set.empty, taggedGrammar.Terminals)
            ||> TagBimap.fold (fun symbolicTerminalNames _ terminal ->
                Set.add (symbolicTerminalName terminal) symbolicTerminalNames)
            // Create a map using the set as the key set, and where each value is None.
            |> Map.ofKeys (fun _ -> None)

        // Emit the symbolic token-name type declaration.
        quickSummary writer "This type is used to give symbolic names to token indexes, useful for error messages."
        unionTypeDecl "tokenId" false symbolicTerminalNamesAndTypes writer
        writer.WriteLine ()

    //
    let private emitSymbolicNonterminalTypeDecl
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (writer : IndentedTextWriter) =
        /// The symbolic nonterminals. All values in this map are None
        /// since the cases don't carry values.
        let symbolicNonterminalNamesAndTypes =
            (Set.empty, taggedGrammar.Nonterminals)
            ||> TagBimap.fold (fun symbolicNonterminalNames _ nonterminal ->
                match nonterminal with
                | AugmentedNonterminal.Start ->
                    // Add a symbolic nonterminal for each of the starting nonterminals.
                    (symbolicNonterminalNames, taggedGrammar.StartNonterminals)
                    ||> TagSet.fold (fun symbolicNonterminalNames startingNonterminalIndex ->
                        match TagBimap.find startingNonterminalIndex taggedGrammar.Nonterminals with
                        | AugmentedNonterminal.Start ->
                            failwith "Unexpectedly found the Start nonterminal in the tagged grammar's set of starting nonterminals."
                        | AugmentedNonterminal.Nonterminal startingNonterminal ->
                            Set.add (symbolicStartingNonterminalName startingNonterminal) symbolicNonterminalNames)

                | AugmentedNonterminal.Nonterminal nonterminal ->
                    Set.add (symbolicNonterminalName nonterminal) symbolicNonterminalNames)
            // Create a map using the set as the key set, and where each value is None.
            |> Map.ofKeys (fun _ -> None)

        // Emit the symbolic nonterminal type declaration.
        quickSummary writer "This type is used to give symbolic names to token indexes, useful for error messages."
        unionTypeDecl "nonterminalId" false symbolicNonterminalNamesAndTypes writer

    // Emit the token -> token-tag function.
    let private emitTokenToTokenTagLookupFunction
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (writer : IndentedTextWriter) =
        quickSummary writer "Maps tokens to integer indexes."
        writer.WriteLine "let private tagOfToken = function"
        IndentedTextWriter.indented writer <| fun writer ->
            // Emit a case for each terminal (token).
            taggedGrammar.Terminals
            |> TagBimap.iter (fun terminalIndex terminal ->
                match terminal with
                | EndOfFile -> ()
                | Terminal terminal ->
                    // Don't emit cases for the built-in (implicit) terminals.
                    if terminal <> errorTerminal then
                        match TagMap.tryFind terminalIndex taggedGrammar.TerminalTypes with
                        | None ->
                            sprintf "| %s -> %i" terminal (untag terminalIndex)
                        | Some _ ->
                            sprintf "| %s _ -> %i" terminal (untag terminalIndex)
                        |> writer.WriteLine)

    // Emit the token-tag -> symbolic-token-name function.
    let private emitTokenTagToSymTokenNameLookupFunction
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (writer : IndentedTextWriter) =
        quickSummary writer "Maps integer indices to symbolic token ids."
        writer.WriteLine "let private tokenTagToTokenId = function"
        IndentedTextWriter.indented writer <| fun writer ->
            // Emit a case for each terminal (token).
            taggedGrammar.Terminals
            |> TagBimap.iter (fun terminalIndex terminal ->
                let symbolicTerminalName = symbolicTerminalName terminal
                sprintf "| %i -> %s" (untag terminalIndex) symbolicTerminalName
                |> writer.WriteLine)

            // Emit a catch-all case to handle invalid values.
            let catchAllVariableName = "tokenIdx"
            writer.WriteLine ("| " + catchAllVariableName + " ->")
            IndentedTextWriter.indented writer <| fun writer ->
                // When the catch-all is matched, it should raise an exception.
                writer.WriteLine (
                    "failwithf \"tokenTagToTokenId: Invalid token. (Tag = %i)\" " + catchAllVariableName)

    // Emit the production-index -> symbolic-nonterminal-name function.
    let private emitProdIdxToSymNonterminalNameLookupFunction
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (writer : IndentedTextWriter) =
        quickSummary writer "Maps production indexes returned in syntax errors to strings representing
                                the non-terminal that would be produced by that production."
        writer.WriteLine "let private prodIdxToNonTerminal = function"
        IndentedTextWriter.indented writer <| fun writer ->
            /// Maps production indices to the symbolic name of the nonterminal produced by each production rule.
            // OPTIMIZE : Change this to just iterate over the productions and emit the cases
            // instead of creating an intermediate map and iterating over it.
            let symbolicNonterminalOfProduction : TagMap<_,string> =
                (TagMap.empty, taggedGrammar.ProductionsByNonterminal)
                ||> TagMap.fold (fun symbolicNonterminalOfProduction nonterminalIndex nonterminalRuleIndices ->
                    // The production rules for the augmented Start symbol need to be handled specially.
                    match TagBimap.find nonterminalIndex taggedGrammar.Nonterminals with
                    | AugmentedNonterminal.Start ->
                        (symbolicNonterminalOfProduction, nonterminalRuleIndices)
                        ||> TagSet.fold (fun symbolicNonterminalOfProductions ruleIndex ->
                            /// The "true" (i.e., non-augmented) nonterminal produced by this rule.
                            let nonterminal =
                                let nonterminalIndex =
                                    match Array.first <| TagMap.find ruleIndex taggedGrammar.Productions with
                                    | Symbol.Nonterminal nonterminalIndex ->
                                        nonterminalIndex
                                    | Symbol.Terminal terminalIndex ->
                                        let msg =
                                            let terminal = TagBimap.find terminalIndex taggedGrammar.Terminals
                                            sprintf "A starting production rule must begin with a nonterminal, but the terminal '%A' was found instead." terminal
                                        raise <| exn msg

                                match TagBimap.find nonterminalIndex taggedGrammar.Nonterminals with
                                | AugmentedNonterminal.Start ->
                                    failwith "Found the Start symbol where a non-augmented nonterminal was expected."
                                | AugmentedNonterminal.Nonterminal nonterminal ->
                                    nonterminal

                            /// The symbolic name for this starting nonterminal.
                            let symbolicStartingNonterminalName = symbolicStartingNonterminalName nonterminal

                            // Add the production-rule-index and symbolic starting nonterminal name to the map.
                            TagMap.add ruleIndex symbolicStartingNonterminalName symbolicNonterminalOfProductions)

                    | AugmentedNonterminal.Nonterminal nonterminal ->
                        let symbolicNonterminalName = symbolicNonterminalName nonterminal
                        (symbolicNonterminalOfProduction, nonterminalRuleIndices)
                        ||> TagSet.fold (fun symbolicNonterminalOfProductions ruleIndex ->
                            TagMap.add ruleIndex symbolicNonterminalName symbolicNonterminalOfProductions))

            // Emit cases based on the production-rule-index -> symbolic-nonterminal-name map.
            symbolicNonterminalOfProduction
            |> TagMap.iter (fun productionRuleIndex nonterminalSymbolicName ->
                sprintf "| %i -> %s" (untag productionRuleIndex) nonterminalSymbolicName
                |> writer.WriteLine)

            // Emit a catch-all case to handle invalid inputs to the function.
            let catchAllVariableName = "prodIdx"
            writer.WriteLine ("| " + catchAllVariableName + " ->")
            IndentedTextWriter.indented writer <| fun writer ->
                // When the catch-all is matched, it should raise an exception.
                writer.WriteLine (
                    "failwithf \"prodIdxToNonTerminal: Invalid production index. (Index = %i)\" " + catchAllVariableName)

    // Emit the token -> token-name function.
    let private emitTokenToTokenNameLookupFunction
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>) (writer : IndentedTextWriter) =
        quickSummary writer "Gets the name of a token as a string."
        writer.WriteLine "let token_to_string = function"
        IndentedTextWriter.indented writer <| fun writer ->
            // Emit a case for each declared terminal (token) --
            // implicit/built-in terminals are skipped.
            taggedGrammar.Terminals
            |> TagBimap.iter (fun terminalIndex terminal ->
                match terminal with
                | AugmentedTerminal.EndOfFile -> ()
                | AugmentedTerminal.Terminal terminal ->
                    // Is this a built-in/implicit terminal?
                    if terminal = errorTerminal then ()
                    else
                        // Data-carrying terminals need to be handled specially.
                        if TagMap.containsKey terminalIndex taggedGrammar.TerminalTypes then
                            sprintf "| %s _ -> \"%s\"" terminal terminal
                        else
                            sprintf "| %s -> \"%s\"" terminal terminal
                        |> writer.WriteLine)

    // Emit the function for getting the token data.
    let private emitTokenDataGetterFunction
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>) (writer : IndentedTextWriter) =
        quickSummary writer "Gets the data carried by a token as an object."
        writer.WriteLine "let private _fsyacc_dataOfToken = function"
        IndentedTextWriter.indented writer <| fun writer ->
            // Emit a case for each declared terminal (token) --
            // implicit/built-in terminals are skipped.
            taggedGrammar.Terminals
            |> TagBimap.iter (fun terminalIndex terminal ->
                match terminal with
                | AugmentedTerminal.EndOfFile -> ()
                | AugmentedTerminal.Terminal terminal ->
                    // Is this a built-in/implicit terminal?
                    if terminal = errorTerminal then ()
                    else
                        match TagMap.tryFind terminalIndex taggedGrammar.TerminalTypes with
                        | None ->
                            sprintf "| %s -> (null : System.Object)" terminal
                        | Some _ ->
                            sprintf "| %s _fsyacc_x -> box _fsyacc_x" terminal
                        |> writer.WriteLine)

    /// Emits F# code declaring terminal (token) and nonterminal types used by the
    /// generated parser into an IndentedTextWriter.
    let emit (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>) (writer : IndentedTextWriter) =
        // Emit the token type declaration.
        emitTokenTypeDecl taggedGrammar writer

        // Emit the symbolic token-name type declaration.
        emitSymbolicTokenNameTypeDecl taggedGrammar writer

        // Emit the symbolic nonterminal type declaration.
        emitSymbolicNonterminalTypeDecl taggedGrammar writer
        writer.WriteLine ()
         
        // Emit the token -> token-tag function.
        emitTokenToTokenTagLookupFunction taggedGrammar writer
        writer.WriteLine ()

        // Emit the token-tag -> symbolic-token-name function.
        emitTokenTagToSymTokenNameLookupFunction taggedGrammar writer
        writer.WriteLine ()

        // Emit the production-index -> symbolic-nonterminal-name function.
        emitProdIdxToSymNonterminalNameLookupFunction taggedGrammar writer
        writer.WriteLine ()

        // Emit constants for "end-of-input" and "tag of error terminal"
        intLiteralDecl "_fsyacc_endOfInputTag" false
            (untag <| TagBimap.findValue AugmentedTerminal.EndOfFile taggedGrammar.Terminals) writer
        intLiteralDecl "_fsyacc_tagOfErrorTerminal" false
            (untag <| TagBimap.findValue (AugmentedTerminal.Terminal errorTerminal) taggedGrammar.Terminals) writer
        writer.WriteLine ()

        // Emit the token -> token-name function.
        emitTokenToTokenNameLookupFunction taggedGrammar writer
        writer.WriteLine ()

        // Emit the function for getting the token data.
        emitTokenDataGetterFunction taggedGrammar writer
        writer.WriteLine ()


/// Functions for computing the parser tables and emitting them into the generated code.
[<RequireQualifiedAccess>]
module internal ParserTables =
    open System.Diagnostics
    open Graham
    open Graham.LR
    open BackendUtils.CodeGen

    (* TODO :   Refactor the functions below -- the 'computeAndEmit' function can handle all of the
                code emission -- the functions for the individual tables should be refactored so they
                only compute and return the table (instead of also emitting it). This'll make it possible
                to implement unit tests for those functions at some later date. *)

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

    /// Computes the GOTO table for the parser, then emits it as a sparse (compressed)
    /// table into the generated parser code.
    let private emitGotoTable startSymbolCount
        (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>) (writer : IndentedTextWriter) =
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
            ||> Map.fold (fun nonterminalIndex _ edges ->
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
    let private emitStateToProductionIndicesTable
        (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>) (writer : IndentedTextWriter) =
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
    let private computeCompressedActionTable
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>) =
        /// The set of all terminals in the augmented grammar (including the fsyacc error terminal).
        let allTerminals =
            (TagSet.empty, taggedGrammar.Terminals)
            ||> TagBimap.fold (fun allTerminals terminalIndex _ ->
                TagSet.add terminalIndex allTerminals)

        //
        (TagMap.empty, parserTable.ActionTable)
        ||> Map.fold (fun parserActionsByState (stateId, terminalIndex) actionSet ->
            match actionSet with
            | Conflict _ ->
                let msg = sprintf "Conflicting actions on terminal %O in state #%i." terminalIndex (int stateId)
                raise <| exn msg
            | Action parserAction ->
                let stateActions =
                    let value = terminalIndex, parserAction
                    match TagMap.tryFind stateId parserActionsByState with
                    | None ->
                        [value]
                    | Some stateActions ->
                        value :: stateActions

                TagMap.add stateId stateActions parserActionsByState)
        //
        |> TagMap.map (fun stateId actions ->
            //
            let terminalsByAction =
                (Map.empty, actions)
                ||> List.fold (fun terminalsByAction (terminal, action) ->
                    let terminals =
                        match Map.tryFind action terminalsByAction with
                        | None ->
                            TagSet.singleton terminal
                        | Some terminals ->
                            TagSet.add terminal terminals

                    Map.add action terminals terminalsByAction)

            /// The most-frequent parser action (if any) for this parser state.
            let mostFrequentAction =
                (None, terminalsByAction)
                ||> Map.fold (fun mostFrequent action terminals ->
                    let terminalCount = TagSet.count terminals
                    match mostFrequent with
                    | None ->
                        Some (action, terminalCount)
                    | Some (_, mostFrequentActionTerminalCount) ->
                        if terminalCount > mostFrequentActionTerminalCount then
                            Some (action, terminalCount)
                        else
                            mostFrequent)
                |> Option.map fst
                |> Option.get

            /// The terminals for which the most-frequent action is taken in this parser state.
            let mostFrequentActionTerminals =
                Map.find mostFrequentAction terminalsByAction

            /// The terminals for which the most-frequent action is NOT taken.
            let otherActionTerminals =
                TagSet.difference allTerminals mostFrequentActionTerminals

            // We only bother "factoring" out the most-frequent action when doing so actually saves space;
            // i.e., when the most-frequent action covers a greater number of terminals than the implicit error action.
            let explicitActionCount =
                // OPTIMIZE : Use TagSet.countWith from ExtCore.
                allTerminals
                |> TagSet.filter (fun terminalIndex ->
                    Map.containsKey (stateId, terminalIndex) parserTable.ActionTable)
                |> TagSet.count

            let mostFrequentActionValue, entries =
                let errorActionCount = (TagSet.count allTerminals) - explicitActionCount
                if TagSet.count mostFrequentActionTerminals <= errorActionCount then
                    // No space savings, leave the error action.
                    let entries =
                        actions
                        // NOTE : The reversal isn't important here since we're going to sort the
                        // array right away anyway. List.revMapIntoArray just avoids creating
                        // an intermediate list with List.map, then calling List.toArray.
                        |> List.revMapIntoArray (fun (terminalIndex, action) ->
                            let action = EnumToValue (actionValue action)
                            (Checked.uint16 terminalIndex), action)
                    entries
                    |> Array.sortInPlaceWith (fun (tag1, _) (tag2, _) ->
                        compare tag1 tag2)

                    EnumToValue ActionValue.Error, entries
                else
                    let entries =
                        otherActionTerminals
                        |> TagSet.toArray
                        |> Array.map (fun terminalIndex ->
                            let action =
                                match Map.tryFind (stateId, terminalIndex) parserTable.ActionTable with
                                | None ->
                                    ActionValue.Error
                                | Some (Action action) ->
                                    actionValue action
                                | Some (Conflict _) ->
                                    let terminal = TagBimap.find terminalIndex taggedGrammar.Terminals
                                    failwithf "Conflicting actions on terminal %O in state #%i." terminal (int stateId)
                            (Checked.uint16 terminalIndex), (EnumToValue action))
                    entries
                    |> Array.sortInPlaceWith (fun (tag1, _) (tag2, _) ->
                        compare tag1 tag2)

                    EnumToValue (actionValue mostFrequentAction), entries

            // The entries for this state.
            Array.append [|
                Checked.uint16 <| Array.length entries;
                mostFrequentActionValue; |]
                (flattenTupleArray entries))

    //
    let private emitActionTable
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>) (writer : IndentedTextWriter) =
        let _fsyacc_actionTableElements, _fsyacc_actionTableRowOffsets =
            //
            let compressedActionTable =
                computeCompressedActionTable taggedGrammar parserTable

            let actionTableElements =
                // Initialize to roughly the correct size (to avoid multiple small reallocations).
                ResizeArray (6 * (TagMap.count compressedActionTable))

            let actionTableRowOffsets = Array.zeroCreate <| TagMap.count compressedActionTable

            compressedActionTable
            |> TagMap.iter (fun stateId elements ->
                actionTableRowOffsets.[int stateId] <- Checked.uint16 <| (ResizeArray.length actionTableElements / 2)
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
    let private emitReductionSymbolCounts
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (writer : IndentedTextWriter) =
        let _fsyacc_reductionSymbolCounts =
            let symbolCounts = Array.zeroCreate <| TagMap.count taggedGrammar.Productions

            let eofTerminalIndex = TagBimap.findValue EndOfFile taggedGrammar.Terminals
            taggedGrammar.Productions
            |> TagMap.iter (fun ruleIndex rule ->
                symbolCounts.[untag ruleIndex] <-
                    // The EndOfFile marker is not included in the count.
                    rule
                    |> Array.countWith (function
                        | Symbol.Nonterminal _ -> true
                        | Symbol.Terminal terminalIndex ->
                            terminalIndex <> eofTerminalIndex)
                    |> Checked.uint16)

            symbolCounts

        oneLineArrayUInt16 "_fsyacc_reductionSymbolCounts" false
            _fsyacc_reductionSymbolCounts writer

    //
    let emitProductionIndexToNonterminalIndexTable
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>) (writer : IndentedTextWriter) =
        let _fsyacc_productionToNonTerminalTable =
            let productionIndexToNonterminalIndexTable =
                Array.zeroCreate (TagMap.count taggedGrammar.Productions)

            taggedGrammar.ProductionsByNonterminal
            |> TagMap.iter (fun nonterminalIndex ruleIndices ->
                ruleIndices
                |> TagSet.iter (fun ruleIndex ->
                    productionIndexToNonterminalIndexTable.[untag ruleIndex] <-
                        Checked.uint16 <| untag nonterminalIndex
                    ))

            // Return the array.
            productionIndexToNonterminalIndexTable

        oneLineArrayUInt16 "_fsyacc_productionToNonTerminalTable" false
            _fsyacc_productionToNonTerminalTable writer

    //
    let emitImmediateActions
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>) (writer : IndentedTextWriter) =
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
    let computeAndEmit (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>) (writer : IndentedTextWriter) =
        (* _fsyacc_action_rows *)
        intLiteralDecl "_fsyacc_action_rows" false
            (TagBimap.count parserTable.ParserStates) writer

        // Emit the GOTO table.
        emitGotoTable (TagSet.count taggedGrammar.StartNonterminals) parserTable writer
            
        // Emit the state->production-indices table.
        emitStateToProductionIndicesTable parserTable writer

        // Emit the ACTION table.
        emitActionTable taggedGrammar parserTable writer
            
        // Emit the reduction symbol counts.
        emitReductionSymbolCounts taggedGrammar writer

        // Emit the production-index->nonterminal-index table.
        emitProductionIndexToNonterminalIndexTable taggedGrammar writer
            
        // Emit the immediate actions table.
        emitImmediateActions taggedGrammar parserTable writer


//
[<RequireQualifiedAccess>]
module private Reductions =
    open Graham
    open Graham.LR
    open BackendUtils.CodeGen

    /// Emits F# code for a single reduction action into an IndentedTextWriter.
    let private reduction (nonterminal : NonterminalIdentifier) (symbols : Symbol<NonterminalIdentifier, TerminalIdentifier>[]) (action : CodeFragment)
        (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (options, writer : IndentedTextWriter) : unit =
        // Write the function declaration for this semantic action.
        options.ParserInterpreterNamespace
        |> Option.fill defaultParsingNamespace
        |> fprintfn writer "(fun (parseState : %s.IParseState) ->"

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
                (* OPTIMIZE :   Use functions from ExtCore.String.Split to re-implement the code below so it doesn't
                                create tons of unnecessary strings. *)
                (* OPTIMIZE :   If the computation of 'trimmedActionLines' were moved down to where it's used, we could
                                use the ExtCore.String.Split functions to eliminate the creation of those strings too --
                                we'd simply adjust the indentation on the substring supplied by the String.Split function
                                then use the substring extension methods from ExtCore to write the adjusted substring
                                into the TextWriter. *)

                /// The individual lines of the reduction action code,
                /// annotated with the number of leading spaces on that line.
                let annotatedActionLines =
                    action.Split (Emit.newlines, System.StringSplitOptions.None)
                    |> Array.map (fun line ->
                        // First replace any tab characters in the string.
                        let line = replaceTabs Emit.indent line
                        let leadingSpaces = countLeadingSpaces line
                        line, leadingSpaces)
        
                /// The minimum number of spaces on the left side of any line of code.
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
                    |> Option.fill GenericZero

                // Remove the same amount of indentation from every non-empty line.
                annotatedActionLines
                |> Array.map (fun (line, leadingSpaces) ->
                    match leadingSpaces with
                    | None ->
                        assert (System.String.IsNullOrWhiteSpace line)
                        String.empty
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
    let emitReductionActions (processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>)
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>) (options, writer : IndentedTextWriter) : unit =
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
                reduction startNonterminal [| Symbol.Nonterminal startSymbol |] defaultAction processedSpec taggedGrammar (options, writer))

            // Emit the actions for each of the production rules.
            processedSpec.ProductionRules
            |> Map.iter (fun nonterminal rules ->
                rules |> Array.iter (fun rule ->
                    /// The rule action, where the symbol placeholders have been replaced by
                    /// the names of variables within the generated code (e.g., $2 changed to _2).
                    let ruleAction =
                        rule.Action
                        |> Option.map replaceSymbolPlaceholders
                        |> Option.fill defaultAction

                    reduction nonterminal rule.Symbols ruleAction processedSpec taggedGrammar (options, writer)))
            
            // Emit the closing bracket of the array.
            writer.WriteLine "|]"

        // Write a blank line for readability.
        writer.WriteLine ()


/// Emit table-driven code which is compatible with the code generated
/// by the older 'fsyacc' tool from the F# PowerPack.
[<RequireQualifiedAccess>]
module private FsYacc =
    open Graham
    open Graham.LR
    open BackendUtils.CodeGen

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
        (taggedGrammar : AugmentedTaggedGrammar<NonterminalIdentifier, TerminalIdentifier, DeclaredType>)
        (parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>)
        (options : FsyaccBackendOptions, writer : IndentedTextWriter) : unit =
        (* Emit the module declaration. *)
        do
            quickSummary writer "Implementation file for parser generated by the fsyacc-compatibility backend for fsharpyacc."

            /// The name of the emitted parser module.
            let parserModuleName =
                options.ModuleName
                |> Option.fill "Parser"
        
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
            header.Split (Emit.newlines, System.StringSplitOptions.None)
            |> Array.iter (fun codeLine ->
                (* TODO :   Trim the lines of code here, as done for the user-specified actions.
                            We'd have to process the entire array first to determine the "base"
                            indentation level, then trim only that much from the front of each string. *)
                writer.WriteLine codeLine)

            // Emit a blank line to separate the header from the compiler-generated parser code.
            writer.WriteLine ())

        // Emit the parser types (e.g., the token type).
        ParserTypes.emit taggedGrammar writer

        // Emit the parser tables.
        ParserTables.computeAndEmit taggedGrammar parserTable writer

        // Emit the reduction functions (i.e., the user-specified actions / code fragments).
        Reductions.emitReductionActions processedSpec taggedGrammar (options, writer)

        do
            // Emit the parser "tables" record and parser functions.
            let typedStartSymbols =
                (Map.empty, processedSpec.StartSymbols)
                ||> Set.fold (fun typedStartSymbols startingNonterminal ->
                    let startSymbolType =
                        Map.find startingNonterminal processedSpec.Nonterminals
                        // Start symbols are required to have a type, so if this breaks
                        // the problem is in the validation stage of the compiler.
                        |> Option.get

                    Map.add startingNonterminal startSymbolType typedStartSymbols)

            tablesRecordAndParserFunctions typedStartSymbols (TagBimap.count taggedGrammar.Terminals) (options, writer)

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
                    new IndentedTextWriter (streamWriter, Emit.indent)

                FsYacc.emit processedSpec taggedGrammar parserTable (fsyaccOptions, indentedTextWriter)

