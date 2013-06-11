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

// TEMP : Remove this once this backend is actually implemented -- it just suppresses unused-variable warnings for now.
#nowarn "1182"


/// A backend which emits a yacc-style "listing" of the items
/// in each state of the compiled parser automaton.
//[<Export(typeof<IBackend>)>]
type TableListingBackend () =
    interface IBackend with
        member this.Invoke (processedSpec, taggedGrammar, parserTable, options) : unit =
            // TODO
            notImpl "TableListingBackend.Invoke"




