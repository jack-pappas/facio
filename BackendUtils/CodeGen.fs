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

//
module BackendUtils.CodeGen


/// Function operators related to the System.IO.TextWriter type.
[<RequireQualifiedAccess>]
module TextWriter =
    open System.IO

    //
    let trailingNewLine (tw : ('W :> TextWriter)) (f : 'W -> 'T) : 'T =
        let result = f tw
        tw.WriteLine ()
        result


/// Functional operators for working with instances of
/// System.CodeDom.Compiler.IndentedTextWriter.
[<RequireQualifiedAccess>]
module IndentedTextWriter =
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


