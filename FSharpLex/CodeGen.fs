(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpLex.CodeGen

open System.CodeDom.Compiler
open System.ComponentModel.Composition
open System.IO
open System.Text
open Ast
open Compile

(* TODO :   Move the code generator (and any other back-ends we want to create)
            into plugins using the Managed Extensibility Framework (MEF). *)

//
[<RequireQualifiedAccess>]
module private IndentedTextWriter =
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
let private indent (itw : IndentedTextWriter) (f : IndentedTextWriter -> 'T) =
    IndentedTextWriter.indent itw
    let result = f itw
    IndentedTextWriter.unindent itw
    result

//
let private generateCode (compiledSpec : CompiledSpecification) (writer : #TextWriter) : unit =
    // Preconditions
    if writer = null then
        nullArg "writer"

    /// Used to create properly-formatted code.
    use indentingWriter = new IndentedTextWriter (writer, "    ")

    // Emit the header (if present).
    compiledSpec.Header
    |> Option.iter indentingWriter.WriteLine

    // Emit the compiled rules
    IndentedTextWriter.indent indentingWriter

    compiledSpec.CompiledRules
    |> Map.iter (fun ruleId compiledRule ->

        // TODO
        raise <| System.NotImplementedException "generateCode"
        ())

    IndentedTextWriter.unindent indentingWriter

    // Emit the footer (if present).
    compiledSpec.Footer
    |> Option.iter indentingWriter.WriteLine

//
let generateString (compiledSpec : CompiledSpecification) =
    //
    let codeStringBuilder = StringBuilder ()
    
    //
    using (new StringWriter (codeStringBuilder)) (generateCode compiledSpec)

    // Return the generated code string.
    codeStringBuilder.ToString ()

