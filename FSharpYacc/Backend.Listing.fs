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


