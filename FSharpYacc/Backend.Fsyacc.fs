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


(* TODO :   Implement the fsyacc-compatible code generator. *)



/// A backend which emits code implementing a table-based pattern matcher
/// compatible with 'fsyacc' and the table interpreters in the F# PowerPack.
[<Export(typeof<IBackend>)>]
type FsyaccBackend () =
    interface IBackend with
        member this.EmitCompiledSpecification (parserSpec, parserTable, options) : unit =
            /// Compilation options specific to this backend.
            let fsyaccOptions =
                match options.FsyaccBackendOptions with
                | None ->
                    raise <| exn "No backend-specific options were provided."
                | Some options ->
                    options

            // TODO : Generate the code and write it to the specified file.
            raise <| System.NotImplementedException "FsyaccBackend.EmitCompiledSpecification"
            //using (File.CreateText fslexOptions.OutputPath) (FsLex.emit compiledSpec options)

