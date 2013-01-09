(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

namespace FSharpLex

(* TODO :   Once we support strongly-typed custom metadata from the backends,
            these types should be moved into their respective backends since they
            won't need to be visible outside of the backends themselves. *)

/// Options to control the behavior of the fslex-compatible backend.
type FslexBackendOptions = {
    /// The output path. The generated code will be written to this file.
    OutputPath : string;
}

/// Graph-based file formats.
type GraphFileFormat =
    /// Directed Graph Markup Language (DGML).
    | Dgml
//    /// The file format used by the 'dot' tool in Graphviz.
//    | GraphvizDot

/// Options to control the behavior of the graph-based backend.
type GraphBackendOptions = {
    /// The output path. The graph data will be written to this file."
    OutputPath : string;
    /// The format to use when serializing the automaton graph.
    Format : GraphFileFormat;
}

(* END: Backend-specific options *)


/// Lexer compilation options.
type CompilationOptions = {
    /// Enable unicode support in the lexer.
    Unicode : bool;

    (* Backend-specific options. *)
    (* TODO :   Once we implement support for strongly-typed custom exports (via MEF)
                from the backends, we can remove these fields because we'll have a better
                (properly encapsulated) way to pass the option values into the backends. *)

    /// Options for the fslex-compatible backend.
    FslexBackendOptions : FslexBackendOptions option;
    /// Options for the graph-based backend.
    GraphBackendOptions : GraphBackendOptions option;
}
