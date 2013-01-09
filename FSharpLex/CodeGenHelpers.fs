(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

/// Helper modules for code-generating backends.
module internal FSharpLex.Plugin.CodeGenerationHelpers


/// Functional operators for working with instances of
/// System.CodeDom.Compiler.IndentedTextWriter.
[<RequireQualifiedAccess>]
module internal IndentedTextWriter =
    open System.CodeDom.Compiler

    //
    let inline indent (itw : IndentedTextWriter) =
        itw.Indent <- itw.Indent + 1

    //
    let inline unindent (itw : IndentedTextWriter) =
        itw.Indent <- max 0 (itw.Indent - 1)

    //
    let indentBounded maxIndentLevel (itw : IndentedTextWriter) =
        // Preconditions
        if maxIndentLevel < 0 then
            invalidArg "maxIndentLevel" "The maximum indent level cannot be less than zero (0)."

        itw.Indent <- min maxIndentLevel (itw.Indent + 1)

    //
    let atIndentLevel absoluteIndentLevel (itw : IndentedTextWriter) (f : IndentedTextWriter -> 'T) =
        // Preconditions
        if absoluteIndentLevel < 0 then
            invalidArg "absoluteIndentLevel" "The indent level cannot be less than zero (0)."

        let originalIndentLevel = itw.Indent
        itw.Indent <- absoluteIndentLevel
        let result = f itw
        itw.Indent <- originalIndentLevel
        result

    //
    let inline indented (itw : IndentedTextWriter) (f : IndentedTextWriter -> 'T) =
        indent itw
        let result = f itw
        unindent itw
        result


// TEMP : This is for compatibility with existing code; it can be removed once all instances
// of 'indent' are replaced with 'IndentedTextWriter.indented'.
open System.CodeDom.Compiler

let inline indent (itw : IndentedTextWriter) (f : IndentedTextWriter -> 'T) =
    IndentedTextWriter.indented itw f


////
//[<RequireQualifiedAccess>]
//module private DocComment =
//    //
//    let summary str (indentingWriter : IndentedTextWriter) =
//
//    //
//    let remarks str (indentingWriter : IndentedTextWriter) =


////
//[<RequireQualifiedAccess>]
//module private DirectlyEncoded =
//    //
//    let emit (compiledSpec : CompiledSpecification) (writer : #TextWriter) : unit =
//        // Preconditions
//        if writer = null then
//            nullArg "writer"
//
//        /// Used to create properly-formatted code.
//        use indentingWriter = new IndentedTextWriter (writer, "    ")
//
//        // Emit the header (if present).
//        compiledSpec.Header
//        |> Option.iter indentingWriter.WriteLine
//
//        // Emit the compiled rules
//        IndentedTextWriter.indent indentingWriter
//
//        compiledSpec.CompiledRules
//        |> Map.iter (fun ruleId compiledRule ->
//
//            // TODO
//            raise <| System.NotImplementedException "generateCode"
//            ())
//
//        IndentedTextWriter.unindent indentingWriter
//
//        // Emit the footer (if present).
//        compiledSpec.Footer
//        |> Option.iter indentingWriter.WriteLine



