(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace FSharpLex.Plugin

open System.ComponentModel.Composition
open FSharpLex
open FSharpLex.Compile

(* TODO :   Determine how the user will select the backend they want to use,
            and also how we can allow backend-specific options to be specified. *)

//
[<Interface>]
type IBackend =
    /// <summary>Invokes this backend to (e.g., emit code) for the given <see cref="CompiledSpecification"/>.</summary>
    /// <param name="compiledSpec">A compiled lexer specification.</param>
    /// <param name="options">Options which control the behavior of the backend.</param>
    abstract EmitCompiledSpecification :
        compiledSpec : CompiledSpecification
        * options : CompilationOptions
        // TODO : Add TextWriter for the backend to write the emitted code into.
        // TODO : Add parameter for logging interface?
        -> unit
