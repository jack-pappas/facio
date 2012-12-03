(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpLex.Emit

open System.ComponentModel.Composition
open Compile

//
[<Interface>]
type IBackend =
    //
    abstract EmitCode :
        compiledSpec : CompiledSpecification
        * options : CompilationOptions
        // TODO : Add TextWriter for the backend to write the emitted code into.
        // TODO : Add parameter for logging interface?
        -> unit

