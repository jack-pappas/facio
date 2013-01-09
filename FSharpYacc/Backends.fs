(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

namespace FSharpYacc.Plugin

open System.ComponentModel.Composition


/// Compiler backends.
[<Export>]
type Backends () =
    let mutable fsyaccBackend = None

    /// The fsyacc-compatible backend.
    [<Import>]
    member __.FsyaccBackend
        with get () : IBackend =
            match fsyaccBackend with
            | None ->
                invalidOp "The fslex backend has not been set."
            | Some backend ->
                backend
        and set value =
            fsyaccBackend <- Some value



