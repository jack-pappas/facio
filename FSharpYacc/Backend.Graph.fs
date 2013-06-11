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

(* TODO :   Move this backend into a separate assembly so the 'FSharpYacc' project
            won't have a dependency on System.Xml.dll. *)
(* TODO :   Implement a backend for the dot (graphviz) format. *)
(* TODO :   Implement a backend which prints a railroad diagram of the grammar.
            https://en.wikipedia.org/wiki/Syntax_diagram *)


// TEMP : Remove this once this backend is actually implemented -- it just suppresses unused-variable warnings for now.
#nowarn "1182"


/// A backend which emits the generated parser automaton in a graph-based format.
//[<Export(typeof<IBackend>)>]
type GraphBackend () =
    interface IBackend with
        member this.Invoke (processedSpec, taggedGrammar, parserTable, options) : unit =
            // TODO
            notImpl "TableListingBackend.Invoke"



