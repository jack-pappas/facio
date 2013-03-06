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

namespace FSharpLex.Plugin

open System.ComponentModel.Composition


/// Compiler backends.
[<Export>]
type Backends () =
    let mutable fslexBackend = None
    let mutable graphBackend = None

    /// The fslex-compatible backend.
    [<Import>]
    member __.FslexBackend
        with get () : IBackend =
            match fslexBackend with
            | None ->
                invalidOp "The fslex backend has not been set."
            | Some backend ->
                backend
        and set value =
            fslexBackend <- Some value

//    /// The graph-based backend.
//    [<Import>]
//    member __.GraphBackend
//        with get () : IBackend =
//            match graphBackend with
//            | None ->
//                invalidOp "The graph backend has not been set."
//            | Some backend ->
//                backend
//        and set value =
//            graphBackend <- Some value

