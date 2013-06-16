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

namespace FSharpYacc

(* TODO :   Once we support strongly-typed custom metadata from the backends,
            these types should be moved into their respective backends since they
            won't need to be visible outside of the backends themselves. *)

/// Options to control the behavior of the fsyacc-compatible backend.
type FsyaccBackendOptions = {
    /// The output path. The generated code will be written to this file.
    OutputPath : string;
    /// The name to use for the generated parser module.
    /// If not set, a default value is used instead.
    ModuleName : string option;
    /// The namespace containing the lexer interpreter.
    /// If not set, a default value is used instead.
    LexerInterpreterNamespace : string option;
    /// The namespace containing the lexer interpreter.
    /// If not set, a default value is used instead.
    ParserInterpreterNamespace : string option;
    /// When generating the parser code, F# 'open' declarations are generated
    /// for these modules/namespace names (in addition to those emitted by default).
    OpenDeclarations : string[];
    /// When set, the parser module will be generated with the 'internal' visibility modifier.
    InternalModule : bool;
}

(* END: Backend-specific options *)


//
type ParserType =
    //
    | Lr0
    //
    | Slr1
    //
    | Lalr1

/// Parser compilation options.
type CompilationOptions = {
    //
    ParserType : ParserType;

    (* Backend-specific options. *)
    (* TODO :   Once we implement support for strongly-typed custom exports (via MEF)
                from the backends, we can remove these fields because we'll have a better
                (properly encapsulated) way to pass the option values into the backends. *)

    /// Options for the fsyacc-compatible backend.
    FsyaccBackendOptions : FsyaccBackendOptions option;
}

