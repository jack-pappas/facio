(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpLex.CodeGen

open System.CodeDom.Compiler
open System.IO
open System.Text
open Ast
open Compile

(* TODO :   Move the code generator (and any other back-ends we want to create)
            into plugins using the Managed Extensibility Framework (MEF). *)


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
    compiledSpec.CompiledRules
    |> Map.iter (fun ruleId compiledRule ->

        // TODO
        raise <| System.NotImplementedException "generateCode"
        ())

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

