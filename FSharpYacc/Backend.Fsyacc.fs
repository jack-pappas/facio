(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

namespace FSharpYacc.Plugin

open System.CodeDom.Compiler
open System.ComponentModel.Composition
open System.IO
open System.Text
open LanguagePrimitives
open FSharpYacc
open FSharpYacc.Ast
open FSharpYacc.Compiler


/// Emit table-driven code which is compatible with the code generated
/// by the older 'fsyacc' tool from the F# PowerPack.
[<RequireQualifiedAccess>]
module private FsYacc =
    open Graham.LR

    //
    let [<Literal>] private defaultLexingNamespace = "Microsoft.FSharp.Text.Lexing"
    //
    let [<Literal>] private defaultParsingNamespace = "Microsoft.FSharp.Text.Parsing"
    /// The namespace where the OCaml-compatible parsers can be found.
    let [<Literal>] private ocamlParsingNamespace = "Microsoft.FSharp.Compatibility.OCaml.Parsing"

    //
    let emit (processedSpec : ProcessedSpecification<_,_>, parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>) (writer : #TextWriter) : unit =
        //



        // TODO
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

            // Generate the code and write it to the specified file.
            using (File.CreateText fsyaccOptions.OutputPath) (FsYacc.emit (processedSpec, parserTable))

