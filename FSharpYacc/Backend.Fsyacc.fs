﻿(*
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
    open System.CodeDom.Compiler
    open Graham.LR
    open BackendUtils.CodeGen

    //
    let [<Literal>] private defaultLexingNamespace = "Microsoft.FSharp.Text.Lexing"
    //
    let [<Literal>] private defaultParsingNamespace = "Microsoft.FSharp.Text.Parsing"
    /// The namespace where the OCaml-compatible parsers can be found.
    let [<Literal>] private ocamlParsingNamespace = "Microsoft.FSharp.Compatibility.OCaml.Parsing"

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

    //
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

        // Emit the production-index -> symbolic-nonterminal-name function.
        quickSummary writer "Maps production indexes returned in syntax errors to strings representing
                             the non-terminal that would be produced by that production."
        writer.WriteLine "let private prodIdxToNonTerminal = function"
        IndentedTextWriter.indented writer <| fun writer ->
            // TODO : Emit a case for each production rule.
            // (Make sure to include a case for the starting production!)

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

        // TODO : Emit the parser tables
        // _fsyacc_gotos
        // _fsyacc_sparseGotoTableRowOffsets
        // _fsyacc_stateToProdIdxsTableElements
        // _fsyacc_stateToProdIdxsTableRowOffsets
        // _fsyacc_action_rows (constant value)
        // _fsyacc_actionTableElements
        // _fsyacc_actionTableRowOffsets
        // _fsyacc_reductionSymbolCounts
        // _fsyacc_productionToNonTerminalTable
        // _fsyacc_immediateActions
        // _fsyacc_reductions

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
