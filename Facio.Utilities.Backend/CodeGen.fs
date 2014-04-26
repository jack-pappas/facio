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

namespace Facio.Utilities.Backend.CodeGen

open System
open System.CodeDom.Compiler
open LanguagePrimitives


/// <summary>
/// Functional operators for working with instances of <see cref="T:System.CodeDom.Compiler.IndentedTextWriter"/>.
/// </summary>
[<RequireQualifiedAccess>]
module IndentedTextWriter =
    open System.CodeDom.Compiler

    //
    [<CompiledName("Indent")>]
    let inline indent (itw : IndentedTextWriter) =
        itw.Indent <- itw.Indent + 1

    //
    [<CompiledName("Unindent")>]
    let inline unindent (itw : IndentedTextWriter) =
        itw.Indent <- max 0 (itw.Indent - 1)

    //
    [<CompiledName("IndentBounded")>]
    let indentBounded maxIndentLevel (itw : IndentedTextWriter) =
        // Preconditions
        if maxIndentLevel < 0 then
            invalidArg "maxIndentLevel" "The maximum indent level cannot be less than zero (0)."

        itw.Indent <- min maxIndentLevel (itw.Indent + 1)

    //
    [<CompiledName("AtIndentLevel")>]
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
    [<CompiledName("Indented")>]
    let inline indented (itw : IndentedTextWriter) (f : IndentedTextWriter -> 'T) =
        indent itw
        let result = f itw
        unindent itw
        result


//
[<AutoOpen>]
module TopLevelOperators =
    // TEMP : This is for compatibility with existing code; it can be removed once all instances
    // of 'indent' are replaced with 'IndentedTextWriter.indented'.
    let inline indent itw f : 'T =
        IndentedTextWriter.indented itw f

    /// Compute the number of consecutive space characters starting at the beginning of a string.
    /// If the string is empty or contains only space characters, this function returns None.
    [<CompiledName("CountLeadingSpaces")>]
    let private countLeadingSpaces str =
        let mutable index = 0
        let mutable foundNonSpace = false
        let len = String.length str
        while index < len && not foundNonSpace do
            // Is the current character a space character?
            if str.[index] = ' ' then
                index <- index + 1
            else
                foundNonSpace <- true

        // If all of the characters in the string are space characters,
        // return None. Note this also correctly handles empty strings.
        if index = len then
            None
        else
            Some <| uint32 index

    /// Replaces the tab characters in a string with some equivalent tab string.
    [<CompiledName("ReplaceTabs")>]
    let inline private replaceTabs tabString (str : string) =
        str.Replace ("\t", tabString)

    /// Split 'actionCode' into multiple lines. Determine the minimum amount of whitespace which appears on the left of any line in the
    /// action, but do not consider blank lines. Then, trim this minimum amount of whitespace from the left side of each line.
    /// When this is done, the action can be written line-by-line using the standard 'writer.WriteLine' method of the IndentedTextWriter,
    /// and the generated code will have the correct indentation.
    [<CompiledName("TrimActionLines")>]
    let trimActionLines (actionCode : string) =
        // Preconditions
        //checkNonNull "actionCode" actionCode

        /// The individual lines of the reduction action code,
        /// annotated with the number of leading spaces on that line.
        let annotatedActionLines =
            // OPTIMIZE : Avoid creating the intermediate array of substrings by using String.Splits.iter from ExtCore.
            actionCode.Split ([| "\r\n"; "\n"; "\r" |], StringSplitOptions.None)
            |> Array.map (fun line ->
                // First replace any tab characters in the string.
                let line = replaceTabs "    " line
                let leadingSpaces = countLeadingSpaces line
                line, leadingSpaces)
        
        /// The minimum number of spaces on the left side of any line of code.
        let minIndentation =
            let minIndentation =
                (None, annotatedActionLines)
                ||> Array.fold (fun x (_, y) ->
                    match x, y with
                    | None, None ->
                        None
                    | (Some _ as x), None ->
                        x
                    | None, (Some _ as y) ->
                        y
                    | Some x, Some y ->
                        Some <| min x y)

            // Default to zero (0) indentation.
            defaultArg minIndentation GenericZero

        // Remove the same amount of indentation from every non-empty line.
        annotatedActionLines
        |> Array.map (fun (line, leadingSpaces) ->
            match leadingSpaces with
            | None ->
                assert (String.IsNullOrWhiteSpace line)
                String.Empty
            | Some _ ->
                // Remove the computed number of spaces from the left side of this line.
                line.Substring (int minIndentation))
