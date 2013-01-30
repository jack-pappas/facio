(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

namespace FSharpYacc.Plugin

open System.ComponentModel.Composition
open System.IO
open System.Text
open FSharpYacc
open FSharpYacc.Ast
open FSharpYacc.Compiler
open Graham
open Graham.Graph

(* TODO :   Move this backend into a separate assembly so the 'fsharplex' project
            won't have a dependency on System.Xml.dll. *)
(* TODO :   Implement a backend for the dot (graphviz) format. *)




/// A backend which emits a yacc-style "listing" of the items
/// in each state of the compiled parser automaton.
//[<Export(typeof<IBackend>)>]
type TableListingBackend () =
    interface IBackend with
        member this.Invoke (processedSpec, parserTable, options) : unit =
            // TODO
            raise <| System.NotImplementedException "TableListingBackend.Invoke"

//            /// Compilation options specific to this backend.
//            let fsyaccOptions =
//                match options.FsyaccBackendOptions with
//                | None ->
//                    raise <| exn "No backend-specific options were provided."
//                | Some options ->
//                    options
//
//            // Generate the code and write it to the specified file.
//            using (File.CreateText fsyaccOptions.OutputPath) <| fun streamWriter ->
//                use indentedTextWriter =
//                    // Set the indentation to the standard F# indent (4 spaces).
//                    new IndentedTextWriter (streamWriter, "    ")
//
//                FsYacc.emit (processedSpec, parserTable) (fsyaccOptions, indentedTextWriter)


