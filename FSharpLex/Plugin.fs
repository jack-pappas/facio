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

open FSharpLex
open FSharpLex.Compile

(* TODO :   Determine how the user will select the backend they want to use,
            and also how we can allow backend-specific options to be specified. *)

//
[<Interface>]
type IBackend =
    /// The name of the backend.
    abstract Name : string with get

    /// <summary>Invokes this backend to (e.g., emit code) for the given <see cref="CompiledSpecification"/>.</summary>
    /// <param name="compiledSpec">A compiled lexer specification.</param>
    /// <param name="options">Options which control the behavior of the backend.</param>
    abstract EmitCompiledSpecification :
        compiledSpec : CompiledSpecification
        * options : CompilationOptions
        // * logger : NLog.Logger
        -> unit
