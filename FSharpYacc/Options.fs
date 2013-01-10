(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

namespace FSharpYacc

(* TODO :   Once we support strongly-typed custom metadata from the backends,
            these types should be moved into their respective backends since they
            won't need to be visible outside of the backends themselves. *)

/// Options to control the behavior of the fsyacc-compatible backend.
type FsyaccBackendOptions = {
    /// The output path. The generated code will be written to this file.
    OutputPath : string;
    /// When set, the parser module will be generated with the 'internal' visibility modifier.
    InternalModule : bool;
    /// The name to use for the generated parser module.
    /// If not set, a default value is used instead.
    ModuleName : string option;
}

(* END: Backend-specific options *)


//
type ParserType =
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

