﻿(*

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

open System.ComponentModel.Composition
open System.IO
open Reggie
open Reggie.SpecializedCollections
open Reggie.Ast
open Reggie.Compile
open Reggie.Plugin

(* TODO :   In the code-generation backends below, where the user-defined semantic actions
            are emitted, it might be useful to add a bit of code which emits a single-line
            comment before emitting the semantic action code when the action will never be
            executed because that action's pattern is overlapped by some earlier pattern.
            E.g., "This code is unreachable because it's pattern will never be matched."
            This would just serve as a reminder to the user later on (after the code is generated)
            in case they don't see the warning message we emit. *)


//
[<AutoOpen>]
module private FsLexConstants =
    //
    let [<Literal>] interpreterVariableName = "_fslex_tables"
    //
    let [<Literal>] transitionTableVariableName = "trans"
    //
    let [<Literal>] actionTableVariableName = "actions"
    //
    let [<Literal>] sentinelValue = System.UInt16.MaxValue
    //
    let [<Literal>] lexerBufferVariableName = "lexbuf"
    //
    let [<Literal>] lexerBufferTypeName = "LexBuffer<_>"
    //
    let [<Literal>] lexingStateVariableName = "_fslex_state"


//
[<AutoOpen>]
module CodeGenHelpers =
    /// Writes an array or list element containing an F# uint16 literal value to a TextWriter.
    let inline writeUInt16LiteralElement (textWriter : TextWriter) (value : uint16) =
        textWriter.Write (uint32 value)
        textWriter.Write "us; "

    /// Compute the number of consecutive space characters starting at the beginning of a string.
    /// If the string is empty or contains only space characters, this function returns None.
    let countLeadingSpaces str =
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


//
[<RequireQualifiedAccess>]
module private LexerDfaGraph =
    /// Creates a map of transitions out of this DFA state, keyed by the character labeling the transition edge.
    // OPTIMIZE : This should use an IntervalMap for better performance.
    // Additionally, it should be created on-the-fly while creating the DFA instead of having to re-compute it here.
    let createTransitionMap (ruleDfaTransitions : Graph.LexerDfaGraph) ruleDfaStateId baseDfaStateId =
        // Not all DFA states have out-transitions; for those states, we return an empty map.
        match TagMap.tryFind ruleDfaStateId ruleDfaTransitions.AdjacencyMap with
        | None ->
            HashMap.empty
        | Some targetMap ->
            // "Pivot" the target map to get a map of char -> target-state.
            // We also map the target-state-ids from their id within this rule's DFA to their id within the combined DFA
            // (i.e., the merged DFA containing the DFAs for all of the defined rules).
            (HashMap.empty, targetMap)
            ||> TagMap.fold (fun outTransitions targetStateRuleDfaStateId edgeChars ->
                // This DFA state's id within the combined DFA.
                let targetStateCombinedStateId = targetStateRuleDfaStateId + baseDfaStateId

                // REVIEW:  Profiling shows that when compiling the F# compiler lexer, over 60% of the
                //          overall compilation time is spent within the closure below.
                (outTransitions, edgeChars)
                ||> CharSet.fold (fun outTransitions c ->
                    HashMap.add c targetStateCombinedStateId outTransitions))


//
[<RequireQualifiedAccess>]
module private AsciiLexer =
    open System.CodeDom.Compiler

    (*  The transition vector for each state in an 'fslex'-compatible ASCII transition
        table has 257 elements. The first 256 elements represent each possible ASCII value;
        the last element represents the 'end-of-file' marker. *)

    /// Emits the elements into an ASCII transition table row for the given DFA state.
    let transitionVectorElements compiledRule ruleDfaStateId baseDfaStateId (indentingWriter : IndentedTextWriter) =
        // Preconditions
        // TODO

        let ruleDfaTransitions = compiledRule.Dfa.Transitions

        /// The transitions out of this DFA state, keyed by the character labeling the transition edge.
        let outTransitions = LexerDfaGraph.createTransitionMap ruleDfaTransitions ruleDfaStateId baseDfaStateId

        // Emit the transition vector elements, based on the transitions out of this state.
        for c = 0 to 255 do
            let targetStateId =
                let targetStateId = HashMap.tryFind (char c) outTransitions

                // If no transition edge was found for this character, return the
                // sentinel value to indicate there's no transition.
                defaultArg targetStateId (tag <| int sentinelValue)

            // Emit the state number of the transition target.
            writeUInt16LiteralElement indentingWriter <| Checked.uint16 targetStateId

        // Emit the element representing the state to transition
        // into when the 'end-of'file' marker is consumed.
        // NOTE : Only the initial DFA state of a rule can consume the EOF marker!
        let eofTransitionTarget =
            if compiledRule.Dfa.InitialState = ruleDfaStateId then
                match ruleDfaTransitions.EofTransitionEdge with
                | None -> sentinelValue
                | Some (_, targetStateId) ->
                    // Remember the target DFA state is _relative_ to this DFA --
                    // add it to the base DFA state id to get it's state id for the combined DFA.
                    Checked.uint16 (targetStateId + baseDfaStateId)
            else sentinelValue

        writeUInt16LiteralElement indentingWriter eofTransitionTarget


//
[<RequireQualifiedAccess>]
module private UnicodeLexer =
    open System.CodeDom.Compiler
    open System.Text
    open Facio.Utilities.Backend.CodeGen

    (*  Each row of a Unicode-based, 'fslex'-compatible transition table contains:
            - 128 entries for the standard ASCII characters
            - n entries comprised of a pair of entries (giving 2*n actual entries);
              These entries represent specific Unicode characters.
            - 30 entries representing Unicode categories (UnicodeCategory)
            - 1 entry representing the end-of-file (EOF) marker.
              
        Caveat: the fslex interpreter expects all of the transition-table rows to have the same number of entries.
        This means 'n' (the number of specific Unicode characters for which we have a transition entry in the table) must be the same
        for all rows in the table; therefore, before we can emit any of the transition-table rows, we first need to examine the
        transitions from all states and compute the set of all specific Unicode characters used to label transitions
        (edges between states). When emitting each transition-table row, we emit transitions to the error state for any of those
        characters which don't actually have a transition out of the current state.
    *)

    //
    let private lowAsciiChars =
        CharSet.ofRange (char 0) (char 127)

    //
    let private optimizeTransitions (targetMap : TagMap<Graph.DfaState, CharSet>) =
        // If 'targetMap' is empty, there's nothing for this function to do, so return empty maps.
        if TagMap.isEmpty targetMap then Map.empty, Map.empty else

        ((Map.empty, Map.empty), UnicodeCharSet.byCategory)
        ||> Map.fold (fun (categoryTransitions, charTransitions) category categoryChars ->
            (*  If there is a transition out of this DFA state for *most* characters in this
                Unicode category and all of those transitions go to the same state, we can compress
                the lexer table by emitting a transition for the Unicode category itself instead
                of the individual characters.
                If we do emit a transition for the category, we also need to emit an individual edge
                for each character which transitions to a different DFA state than the one used by
                the whole category (or the sentinel value to indicate no transition for that character). *)

            // Remove any low ASCII characters out of this category's character set.
            // They always have transition entries in the table and so they don't need to be handled by this function.
            let categoryChars =
                CharSet.difference categoryChars lowAsciiChars

            /// The DFA states targeted by transitions labeled with characters from this Unicode class.
            let categoryTargetMap =
                // NOTE : As of ExtCore 0.8.41, there might be something funny going on with TagMap.map.
                // It doesn't seem to work here; the program doesn't crash but the fold below always acts as if
                // 'categoryTargetMap' is empty, and the VS debugger can't display the map.
//                targetMap
//                |> TagMap.map (fun _ edgeChars ->
//                    CharSet.intersect categoryChars edgeChars)
                (TagMap.empty, targetMap)
                ||> TagMap.fold (fun categoryTargetMap target edgeChars ->
                    TagMap.add target (CharSet.intersect categoryChars edgeChars) categoryTargetMap)

            /// The set of characters in this Unicode category which do not label a transition out of the current DFA state.
            let errorChars =
                (categoryChars, categoryTargetMap)
                ||> TagMap.fold (fun categoryChars _ edgeChars ->
                    CharSet.difference categoryChars edgeChars)

            /// The DFA state targeted by the greatest number of edges labeled with characters from this Unicode category.
            let categoryTarget =
                // Use the error state and the number of invalid characters for this state as the initial values for this fold.
                // This means that the category transition will target the error state (and all other characters in the category
                // require individual transitions) unless we find a set of characters from this category which is larger than the
                // set of invalid characters for this state and which also target the same DFA state.
                let errorWeight = CharSet.count errorChars

                ((tag <| int sentinelValue, errorWeight), categoryTargetMap)
                ||> TagMap.fold (fun (bestTarget, maxWeight) target edgeChars ->
                    let weight = CharSet.count edgeChars
                    if weight > maxWeight then
                        target, weight
                    else
                        bestTarget, maxWeight)
                // Discard the weight value, keeping the target state id.
                |> fst

            // Add transitions to the maps based on whether the category target state is the error state.
            if categoryTarget = (tag <| int sentinelValue) then
                // Add transitions for all valid transition characters from this state.
                let charTransitions =
                    // Fold over 'categoryTargetMap' to add individual character transitions for characters in
                    // this Unicode category which target a state which is not 'categoryTarget'.
                    (charTransitions, categoryTargetMap)
                    ||> TagMap.fold (fun charTransitions targetStateId edgeChars ->
                        (charTransitions, edgeChars)
                        ||> CharSet.fold (fun charTransitions c ->
                            Map.add c targetStateId charTransitions))

                categoryTransitions, charTransitions

            else
                // Add the DFA state targeted by the greatest number of edges labeled with
                // characters in this Unicode category to the category-transition-target map.
                let categoryTransitions = Map.add category categoryTarget categoryTransitions
                
                let charTransitions =
                    // Fold over 'categoryTargetMap' to add individual character transitions for characters in
                    // this Unicode category which target a state which is not 'categoryTarget'.
                    (charTransitions, categoryTargetMap)
                    ||> TagMap.fold (fun charTransitions targetStateId edgeChars ->
                        if targetStateId = categoryTarget then
                            charTransitions
                        else
                            (charTransitions, edgeChars)
                            ||> CharSet.fold (fun charTransitions c ->
                                Map.add c targetStateId charTransitions))
            
                let charTransitions =
                    (charTransitions, errorChars)
                    ||> CharSet.fold (fun charTransitions c ->
                        Map.add c (tag <| int sentinelValue) charTransitions)
                    
                categoryTransitions, charTransitions)

    //
    let transitionChars (compiledRules : Map<RuleIdentifier, CompiledRule>) =
        (CharSet.empty, compiledRules)
        ||> Map.fold (fun transitionChars _ compiledRule ->
            let ruleDfaTransitions = compiledRule.Dfa.Transitions

            let ruleDfaStateCount = ruleDfaTransitions.VertexCount

            (0, ruleDfaStateCount - 1, transitionChars)
            |||> Range.fold (fun transitionChars ruleDfaStateId ->
                //
                let _, unicodeCharTransitions =
                    // Get the target map for this DFA state (i.e., the inner map within the DFA graph adjacency map).
                    ruleDfaTransitions.AdjacencyMap
                    |> TagMap.tryFind (tag ruleDfaStateId)
                    |> Option.fill TagMap.empty
                    |> optimizeTransitions

                (transitionChars, unicodeCharTransitions)
                ||> Map.fold (fun transitionChars c _ ->
                    CharSet.add c transitionChars)))

    /// Emits the elements into a Unicode transition table row for the given DFA state.
    let transitionVectorElements unicodeTransitionChars compiledRule ruleDfaStateId baseDfaStateId (indentingWriter : IndentedTextWriter) =
        // Preconditions
        // TODO

        let ruleDfaTransitions =
            compiledRule.Dfa.Transitions

        let outTransitions =
            LexerDfaGraph.createTransitionMap ruleDfaTransitions ruleDfaStateId baseDfaStateId

        // Emit the transition vector elements for the lower range of ASCII elements [0-127].
        for c = 0 to 127 do
            // Determine the id of the state we transition to when this character is the input.
            let targetStateId =
                outTransitions
                |> HashMap.tryFind (char c)
                // If no transition edge was found for this character, return the
                // sentinel value to indicate there's no transition.
                |> Option.fill (tag <| int sentinelValue)

            // Emit the state number of the transition target.
            writeUInt16LiteralElement indentingWriter <| Checked.uint16 targetStateId

        //
        let unicodeCategoryTransitions, unicodeCharTransitions =
            ruleDfaTransitions.AdjacencyMap
            |> TagMap.tryFind ruleDfaStateId
            |> Option.fill TagMap.empty
            |> optimizeTransitions

        // Emit entries for specific Unicode elements.
        // Note that fslex requires the transition vectors for every state in the DFA to contain the same number
        // of entries for specific Unicode characters, so we may need to emit entries for characters which don't
        // label a transition edge from this state (in that case, we emit an entry which transitions to the error state).
        unicodeTransitionChars
        |> CharSet.iter (fun c ->
            // The state targeted by the transition edge labeled by 'c'.
            let targetStateId =
                // First, check to see if this state has a specific Unicode transition for 'c'.
                unicodeCharTransitions
                |> Map.tryFind c
                // If there wasn't a specific transition for this character, is there a transition
                // for this character's Unicode category?
                |> Option.tryFillWith (fun () ->
                    let category = System.Globalization.CharUnicodeInfo.GetUnicodeCategory c
                    Map.tryFind category unicodeCategoryTransitions)
                // If this state doesn't have an out-transition-edge labeled with 'c',
                // transition to the error state (by using the sentinel value as the target state id).
                |> Option.fill (tag <| int sentinelValue)

            // Emit the character itself (as a uint16).
            writeUInt16LiteralElement indentingWriter <| uint16 c

            // Emit the target state ID.
            writeUInt16LiteralElement indentingWriter <| Checked.uint16 targetStateId)

        // Emit entries for Unicode categories.
        for i = 0 to 29 do
            let targetStateId =
                unicodeCategoryTransitions
                |> Map.tryFind (enum i)
                |> Option.fill (tag <| int sentinelValue)

            // Emit the state number of the transition target.
            writeUInt16LiteralElement indentingWriter <| Checked.uint16 targetStateId

        // Emit the element representing the state to transition
        // into when the 'end-of'file' marker is consumed.
        // NOTE : Only the initial DFA state of a rule can consume the EOF marker!
        let eofTransitionTarget =
            if compiledRule.Dfa.InitialState = ruleDfaStateId then
                match ruleDfaTransitions.EofTransitionEdge with
                | None -> sentinelValue
                | Some (_, targetStateId) ->
                    // Remember the target DFA state is _relative_ to this DFA --
                    // add it to the base DFA state id to get it's state id for the combined DFA.
                    Checked.uint16 (targetStateId + baseDfaStateId)
            else sentinelValue

        writeUInt16LiteralElement indentingWriter eofTransitionTarget


/// Emit table-driven code which is compatible to the code generated by the older 'fslex' tool.
[<RequireQualifiedAccess>]
module private FsLex =
    open System.CodeDom.Compiler
    open System.Text
    open Facio.Utilities.Backend.CodeGen

    //
    let private emitTransitionTable (compiledRules : Map<RuleIdentifier, CompiledRule>) (options : CompilationOptions) (indentingWriter : IndentedTextWriter) =
        // Documentation comments for the transition table.
        "/// <summary>Transition table.</summary>" |> indentingWriter.WriteLine
        "/// <remarks>" |> indentingWriter.WriteLine
        "/// The state number is the first index (i.e., the index of the outer array)." |> indentingWriter.WriteLine
        "/// The value of the next character (expanded to an integer) in the input stream is the second index." |> indentingWriter.WriteLine
        "/// Given a state number and a character value, this table returns the state number of" |> indentingWriter.WriteLine
        "/// the next state to transition to." |> indentingWriter.WriteLine
        "/// </remarks>" |> indentingWriter.WriteLine

        // Emit the "let" binding for the transition table.
        sprintf "let %s : uint16[] array =" transitionTableVariableName
        |> indentingWriter.WriteLine

        // Indent the body of the "let" binding for the transition table.
        IndentedTextWriter.indented indentingWriter <| fun indentingWriter ->
            // Opening bracket of the array.
            indentingWriter.WriteLine "[|"

            /// The function to use to emit the transition vector for each DFA state.
            // In 'fslex', the length of the transition vector depends on whether
            // or not the lexer is generated with support for Unicode.
            let stateTransitionEmitter =
                if options.Unicode then
                    /// The set of Unicode transition chars used to label state-transition-edges,
                    /// minus the low ASCII characters and complete Unicode categories.
                    let specificUnicodeChars = UnicodeLexer.transitionChars compiledRules
                    UnicodeLexer.transitionVectorElements specificUnicodeChars
                else
                    AsciiLexer.transitionVectorElements

            // Emit the transition vector for each state in the combined DFA.
            (0, compiledRules)
            ||> Map.fold (fun baseDfaStateId ruleId compiledRule ->
                // Emit a comment with the name of the rule.
                sprintf "(*** Rule: %s ***)" ruleId
                |> indentingWriter.WriteLine

                let ruleDfaTransitions = compiledRule.Dfa.Transitions
                let ruleDfaStateCount = ruleDfaTransitions.VertexCount

                // Write the transition vectors for the states in this rule's DFA.
                for ruleDfaStateId = 0 to ruleDfaStateCount - 1 do
                    // Emit a comment with the state number (in the overall combined DFA).
                    sprintf "(* State %i *)" <| baseDfaStateId + ruleDfaStateId
                    |> indentingWriter.WriteLine

                    // Emit the opening bracket of the transition vector for this state.
                    indentingWriter.Write "[| "

                    // Emit the transition vector elements, based on the transitions out of this state.
                    stateTransitionEmitter compiledRule (tag ruleDfaStateId) (tag baseDfaStateId) indentingWriter

                    // Emit the closing bracket of the transition vector for this state,
                    // plus a semicolon to separate it from the next state's transition vector.
                    indentingWriter.WriteLine "|];"

                // Advance to the next rule.
                baseDfaStateId + ruleDfaStateCount)
            // Discard the state id accumulator, it's no longer needed.
            |> ignore

            // Closing bracket of the array.
            indentingWriter.WriteLine "|]"

    //
    let private emitActionTable (compiledRules : Map<RuleIdentifier, CompiledRule>) (indentingWriter : IndentedTextWriter) =
        // Documentation comments for the action table.
        "/// <summary>The action table.</summary>" |> indentingWriter.WriteLine

        // Emit the "let" binding for the action table.
        sprintf "let %s : uint16[] = [| " actionTableVariableName
        |> indentingWriter.WriteLine

        // Indent the body of the "let" binding for the action table.
        IndentedTextWriter.indented indentingWriter <| fun indentingWriter ->
            (0, compiledRules)
            ||> Map.fold (fun ruleStartingStateId ruleId compiledRule ->
                // Write a comment with the name of this rule.
                sprintf "(*** Rule: %s ***)" ruleId
                |> indentingWriter.WriteLine

                let ruleDfaTransitions = compiledRule.Dfa.Transitions
                /// The number of states in this rule's DFA.
                let ruleDfaStateCount = ruleDfaTransitions.VertexCount

                for dfaStateId = 0 to ruleDfaStateCount - 1 do
                    // Determine the index of the rule clause accepted by this DFA state (if any).
                    compiledRule.Dfa.RuleClauseAcceptedByState
                    |> Map.tryFind (tag dfaStateId)
                    // If this state accepts a rule clause, convert the clause index to a uint16.
                    |> Option.map Checked.uint16
                    // If this state isn't a final (accepting) state, emit the sentinel value to indicate that.
                    |> Option.fill sentinelValue
                    // Emit the accepted rule number.
                    |> writeUInt16LiteralElement indentingWriter

                // End the line containing the transition elements for this rule.
                indentingWriter.WriteLine ()

                // Update the starting state ID for the next rule.
                ruleStartingStateId + ruleDfaStateCount)
            // Discard the threaded state ID counter
            |> ignore

            // Emit the closing bracket for the array.
            indentingWriter.WriteLine "|]"

    //
    let private emitTables (compiledRules : Map<RuleIdentifier, CompiledRule>) (options : CompilationOptions) (indentingWriter : IndentedTextWriter) =
        // Preconditions
        // TODO

        // Emit the 'let' binding for the fslex "Tables" object.
        "/// Interprets the transition and action tables of the lexer automaton."
        |> indentingWriter.WriteLine

        sprintf "let private %s =" interpreterVariableName
        |> indentingWriter.WriteLine

        // Indent the body of the "let" binding.
        IndentedTextWriter.indented indentingWriter <| fun indentingWriter ->
            // Emit the transition table.
            emitTransitionTable compiledRules options indentingWriter
            indentingWriter.WriteLine ()

            // Emit the action table.
            emitActionTable compiledRules indentingWriter
            indentingWriter.WriteLine ()

            // Emit code to create the interpreter object.
            "// Create the interpreter from the transition and action tables."
            |> indentingWriter.WriteLine

            // TEMP : Pass the compilation options in a better way here -- we've already checked that the CompilationOptions record
            //        includes an FslexBackendOptions record, so we shouldn't need to use Option.get here.
            let lexerLibraryNamespace =
                let fslexOptions = Option.get options.FslexBackendOptions
                fslexOptions.LexerLibraryNamespace

            sprintf "%s.%s.Create (%s, %s)"
                lexerLibraryNamespace
                (if options.Unicode then "UnicodeTables" else "AsciiTables")
                transitionTableVariableName
                actionTableVariableName
            |> indentingWriter.WriteLine

    /// Emits the code for the functions which execute the semantic actions of the rules.
    let private ruleFunctions (compiledRules : Map<RuleIdentifier, CompiledRule>) (options : CompilationOptions) (indentingWriter : IndentedTextWriter) =
        // Preconditions
        // TODO

        // TODO : Pass the CompilationOptions in a better way here -- we've already checked to make sure the record
        //        contains an FslexBackendOptions record, so we shouldn't need to use Option.get here.
        let lexerLibraryNamespace =
            let fslexOptions = Option.get options.FslexBackendOptions
            fslexOptions.LexerLibraryNamespace

        ((0, true), compiledRules)
        ||> Map.fold (fun (ruleStartingStateId, isFirstRule) ruleId compiledRule ->
            // Emit a comment with the name of this rule.
            sprintf "(* Rule: %s *)" ruleId
            |> indentingWriter.WriteLine

            // Emit the let-binding for this rule's function.
            fprintf indentingWriter "%s %s " (if isFirstRule then "let rec" else "and") ruleId

            // Emit parameter names
            compiledRule.Parameters
            |> Array.iter (fun paramName ->
                indentingWriter.Write paramName
                indentingWriter.Write ' ')

            // Emit the lexer buffer parameter as the last (right-most) parameter.
            sprintf "(%s : %s.%s) ="
                lexerBufferVariableName
                lexerLibraryNamespace
                lexerBufferTypeName
            |> indentingWriter.WriteLine

            // Indent and emit the body of the function.
            IndentedTextWriter.indented indentingWriter <| fun indentingWriter ->
                // Emit the "let" binding for the inner function.
                fprintf indentingWriter "let _fslex_%s " ruleId

                // Emit parameter names
                compiledRule.Parameters
                |> Array.iter (fun paramName ->
                    indentingWriter.Write paramName
                    indentingWriter.Write ' ')

                // Emit the lexer-state and lexer buffer parameters.
                sprintf "%s %s =" lexingStateVariableName lexerBufferVariableName
                |> indentingWriter.WriteLine

                // Indent and emit the body of the inner function, which is essentially
                // a big "match" statement which calls the user-defined semantic actions.
                IndentedTextWriter.indented indentingWriter <| fun indentingWriter ->
                    // Emit the top of the "match" statement.
                    sprintf "match %s.Interpret (%s, %s) with"
                        interpreterVariableName
                        lexingStateVariableName
                        lexerBufferVariableName
                    |> indentingWriter.WriteLine

                    // Emit the match patterns (which are just the indices of the rules),
                    // and within them emit the user-defined semantic action code.
                    compiledRule.RuleClauseActions
                    |> Array.iteri (fun ruleClauseIndex actionCode ->
                        // Emit the index as a match pattern.
                        fprintf indentingWriter "| %i ->" ruleClauseIndex   // 'Write', not 'WriteLine' (see comment below).

                        // Indent again to emit the user-action code for this rule.
                        // Due to a small bug in IndentedTextWriter, a change in indentation only takes effect after WriteLine()
                        // is called. Therefore, we emit the newline for the match pattern after the indent level has been changed,
                        // so the indentation takes effect "immediately".
                        IndentedTextWriter.indented indentingWriter <| fun indentingWriter ->
                            // Emit the newline for the match pattern.
                            indentingWriter.WriteLine ()

                            // Emit an F# #line directive for the user-defined code;
                            // this allows the F# compiler to emit warning/error messages referencing
                            // the user-defined code's original location in the lexer spec if necessary.
                            match actionCode.PositionRange with
                            | None -> ()
                            | Some range ->
                                let directiveText =
                                    if String.isNullOrEmpty range.Filename then
                                        sprintf "#line %i" range.First.Line
                                    else
                                        sprintf "#line %i @\"%s\"" range.First.Line range.Filename

                                indentingWriter.WriteLineNoTabs directiveText

                            // Emit the user-defined code for this pattern's semantic action.
                            // This has to be done line-by-line so the indenting is correct!
                            // The lines of the action code are split and trimmed specially to preserve
                            // relative indentation levels between lines.
                            actionCode.Value.ToString()
                            |> trimActionLines
                            |> Array.iter indentingWriter.WriteLine)

                    // Emit a catch-all pattern to handle possible errors.
                    indentingWriter.WriteLine "| invalidAction ->"
                    IndentedTextWriter.indented indentingWriter <| fun indentingWriter ->
                        sprintf "failwithf \"Invalid action index (%%i) specified for the '%s' lexer rule.\" invalidAction" (string ruleId)
                        |> indentingWriter.WriteLine

                // Emit a newline before emitting the call to the inner function.
                indentingWriter.WriteLine ()

                // Emit the call to the inner function.
                fprintf indentingWriter "_fslex_%s " ruleId
                
                compiledRule.Parameters
                |> Array.iter (fun paramName ->
                    indentingWriter.Write paramName
                    indentingWriter.Write ' ')
                
                sprintf "%i %s"
                    (ruleStartingStateId + int compiledRule.Dfa.InitialState)
                    lexerBufferVariableName
                |> indentingWriter.WriteLine

                // Emit a newline before emitting the next rule's function.
                indentingWriter.WriteLine ()

            // Update the starting state ID for the next rule.
            ruleStartingStateId + compiledRule.Dfa.Transitions.VertexCount,
            // The "isFirstRule" flag is always false after the first rule is emitted.
            false)
        // Discard the flag
        |> ignore

    //
    let emit (compiledSpec : CompiledSpecification, options : CompilationOptions) (writer : #TextWriter) : unit =
        // Preconditions
        if writer = null then
            nullArg "writer"

        /// Used to create properly-formatted code.
        use indentingWriter = new IndentedTextWriter (writer, "    ")

        // Emit the header (if present).
        compiledSpec.Header
        |> Option.iter (fun header ->
            indentingWriter.WriteLine header.Value)

        // Emit a newline before emitting the table-driven code.
        indentingWriter.WriteLine ()

        // Emit the transition/action table for the DFA.
        emitTables compiledSpec.CompiledRules options indentingWriter
        assert (indentingWriter.Indent = 0) // Make sure indentation was reset

        // Emit a newline before emitting the semantic action functions.
        indentingWriter.WriteLine ()

        // Emit the semantic functions for the rules.
        ruleFunctions compiledSpec.CompiledRules options indentingWriter
        assert (indentingWriter.Indent = 0) // Make sure indentation was reset

        // Emit a newline before emitting the footer.
        indentingWriter.WriteLine ()

        // Emit the footer (if present).
        compiledSpec.Footer
        |> Option.iter (fun footer ->
            indentingWriter.WriteLine footer.Value)


/// A backend which emits code implementing a table-based pattern matcher
/// compatible with 'fslex' and the table interpreters in the F# PowerPack.
[<Export(typeof<IBackend>)>]
type FslexBackend () =
    interface IBackend with
        member __.Name = typeof<FslexBackend>.Name

        member this.EmitCompiledSpecification (compiledSpec, options) : unit =
            /// Compilation options specific to this backend.
            let fslexOptions =
                match options.FslexBackendOptions with
                | None ->
                    raise <| exn "No backend-specific options were provided."
                | Some options ->
                    options

            // Generate the code and write it to the specified file.
            using (File.CreateText fslexOptions.OutputPath) (FsLex.emit (compiledSpec, options))
