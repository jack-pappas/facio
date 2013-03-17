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
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpLex.Compile

open System.Diagnostics
open LanguagePrimitives
open ExtCore
open ExtCore.Collections
open ExtCore.Control
open ExtCore.Control.Cps
open FSharpLex.SpecializedCollections
open FSharpLex.Graph
open FSharpLex.Regex
open FSharpLex.Ast


/// DFA compilation state.
[<DebuggerDisplay(
    "States = {Transitions.VertexCount}, \
     Final States = {FinalStates.Count}, \
     Transition Sets = {Transitions.EdgeSetCount}")>]
type private CompilationState = {
    //
    Transitions : LexerDfaGraph;
    /// Final (accepting) DFA states.
    // OPTIMIZE : Use the TagSet type from ExtCore.
    FinalStates : Set<DfaStateId>;
    /// Maps regular vectors to the DFA state representing them.
    RegularVectorToDfaState : Map<RegularVector, DfaStateId>;
    /// Maps a DFA state to the regular vector it represents.
    // OPTIMIZE : Use the TagMap type from ExtCore.
    DfaStateToRegularVector : Map<DfaStateId, RegularVector>;
}

/// Functional operators related to the CompilationState record.
/// These operators are designed to adhere to either the Reader or State monads.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private CompilationState =
    /// Empty compilation state.
    let empty = {
        Transitions = LexerDfaGraph.empty;
        FinalStates = Set.empty;
        RegularVectorToDfaState = Map.empty;
        DfaStateToRegularVector = Map.empty; }

    //
    let inline tryGetDfaState regVec (compilationState : CompilationState) =
        Map.tryFind regVec compilationState.RegularVectorToDfaState

    //
    let inline getRegularVector dfaState (compilationState : CompilationState) =
        Map.find dfaState compilationState.DfaStateToRegularVector

    //
    let createDfaState regVec (compilationState : CompilationState) =
        // Preconditions
        // TODO

        Debug.Assert (
            not <| Map.containsKey regVec compilationState.RegularVectorToDfaState,
            "The compilation state already contains a DFA state for this regular vector.")

        /// The DFA state representing this regular vector.
        let (dfaState : DfaStateId), transitions =
            LexerDfaGraph.createVertex compilationState.Transitions

        // Add the new DFA state to the compilation state.
        let compilationState =
            { compilationState with
                Transitions = transitions;
                FinalStates =
                    // A regular vector represents a final state iff it is nullable.
                    if RegularVector.isNullable regVec then
                        Set.add dfaState compilationState.FinalStates
                    else
                        compilationState.FinalStates;
                RegularVectorToDfaState =
                    Map.add regVec dfaState compilationState.RegularVectorToDfaState;
                DfaStateToRegularVector =
                    Map.add dfaState regVec compilationState.DfaStateToRegularVector;
                 }

        // Return the new DFA state and the updated compilation state.
        dfaState, compilationState

//
let private transitions regularVector (transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState) derivativeClass =
    // Ignore empty derivative classes.
    if CharSet.isEmpty derivativeClass then
        transitionsFromCurrentDfaState,
        unvisitedTransitionTargets,
        compilationState
    else
        // The derivative of the regular vector w.r.t. the chosen element.
        let regularVector' =
            // Choose an element from the derivative class; any element
            // will do (which is the point behind the derivative classes).
            let derivativeClassElement = CharSet.minElement derivativeClass

            regularVector
            // Compute the derivative of the regular vector
            |> RegularVector.derivative derivativeClassElement
            // Canonicalize the derivative vector.
            // THIS IS EXTREMELY IMPORTANT -- this algorithm absolutely
            // will not work without this step.
            |> RegularVector.canonicalize

        (*  If the derivative of the regular vector represents the 'error' state,
            ignore it. Instead of representing the error state with an explicit state
            and creating transition edges to it, we will just handle it in the
            back-end (code-generation phase) by transitioning to the error state
            whenever we see an input which is not explicitly allowed.
            This greatly reduces the number of edges in the transition graph. *)
        if RegularVector.isEmpty regularVector' then
            transitionsFromCurrentDfaState,
            unvisitedTransitionTargets,
            compilationState
        else
            let targetDfaState, unvisitedTransitionTargets, compilationState =
                let maybeDfaState =
                    CompilationState.tryGetDfaState regularVector' compilationState

                match maybeDfaState with
                | Some targetDfaState ->
                    targetDfaState,
                    unvisitedTransitionTargets,
                    compilationState
                | None ->
                    // Create a DFA state for this regular vector.
                    let newDfaState, compilationState =
                        CompilationState.createDfaState regularVector' compilationState

                    // Add this new DFA state to the set of unvisited states
                    // targeted by transitions from the current DFA state.
                    let unvisitedTransitionTargets =
                        Set.add newDfaState unvisitedTransitionTargets

                    newDfaState,
                    unvisitedTransitionTargets,
                    compilationState

            //
            let transitionsFromCurrentDfaState =
                Map.add derivativeClass targetDfaState transitionsFromCurrentDfaState

            transitionsFromCurrentDfaState,
            unvisitedTransitionTargets,
            compilationState

//
let rec private createDfa pending compilationState =
    // If there are no more pending states, we're finished compiling.
    if Set.isEmpty pending then
        compilationState
    else
        //
        let currentState = Set.minElement pending
        let pending = Set.remove currentState pending

        //
        let regularVector = CompilationState.getRegularVector currentState compilationState

        // If this regular vector represents the error state, there's nothing to do
        // for it -- just continue processing the worklist.
        if RegularVector.isEmpty regularVector then
            createDfa pending compilationState
        else
            /// The approximate set of derivative classes of the regular vector,
            /// representing transitions out of the DFA state representing it.
            let derivativeClasses = RegularVector.derivativeClasses regularVector

            // For each DFA state (regular vector) targeted by a transition (derivative class),
            // add the DFA state to the compilation state (if necessary), then add an edge
            // to the transition graph from this DFA state to the target DFA state.
            let transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState =
                ((Map.empty, Set.empty, compilationState), derivativeClasses.Elements)
                ||> CharSet.fold (fun state element ->
                    // TEMP : The Elements field of DerivativeClasses needs to be redefined
                    // because it is possible for a class to contain multiple values.
                    let derivClass = CharSet.singleton element
                    transitions regularVector state derivClass)

            // Add any newly-created, unvisited states to the
            // set of states which still need to be visited.
            let pending = Set.union pending unvisitedTransitionTargets

            let compilationState =
                { compilationState with
                    Transitions =
                        // Add the unvisited transition targets to the transition graph.
                        (compilationState.Transitions, transitionsFromCurrentDfaState)
                        ||> Map.fold (fun transitions derivativeClass target ->
                            LexerDfaGraph.addEdges currentState target derivativeClass transitions); }

            // Continue processing recursively.
            createDfa pending compilationState


/// A deterministic finite automaton (DFA) implementing a lexer rule.
[<DebuggerDisplay(
    "States = {Transitions.VertexCount}, \
     Transitions = {Transitions.EdgeSetCount}")>]
type LexerRuleDfa = {
    /// The transition graph of the DFA.
    Transitions : LexerDfaGraph;
    /// For each accepting state of the DFA, specifies the
    /// index of the rule-clause accepted by the state.
    // OPTIMIZE : Use the TagMap type from ExtCore.
    RuleClauseAcceptedByState : Map<DfaStateId, RuleClauseIndex>;
    /// The initial state of the DFA.
    InitialState : DfaStateId;
}

/// A compiled lexer rule.
type CompiledRule = {
    /// The DFA compiled from the patterns of the rule clauses.
    Dfa : LexerRuleDfa;
    /// The formal parameters of the rule.
    Parameters : string[];
    /// The semantic actions to be executed when the
    /// rule clauses are matched.
    RuleClauseActions : CodeFragment[];
}

//
let private rulePatternsToDfa (rulePatterns : RegularVector) (patternIndices : RuleClauseIndex[]) (options : CompilationOptions) : LexerRuleDfa =
    // Preconditions
    if Array.isEmpty rulePatterns then
        invalidArg "rulePatterns" "The rule must contain at least one (1) pattern."
    elif Array.length rulePatterns <> Array.length patternIndices then
        invalidArg "patternIndices" "The array must have the same length as 'rulePatterns'."

    // The initial DFA compilation state.
    let initialDfaStateId, compilationState =
        // Canonicalize the patterns before creating a state for them.
        let rulePatterns = RegularVector.canonicalize rulePatterns

        CompilationState.empty
        |> CompilationState.createDfaState rulePatterns

    // Compile the DFA.
    let compilationState =
        let initialPending = Set.singleton initialDfaStateId
        createDfa initialPending compilationState

    //
    let clausesAcceptedByDfaState : Map<_, Set<RuleClauseIndex>> =
        compilationState.FinalStates
        |> Map.ofKeys (fun finalDfaStateId ->
            // Get the regular vector represented by this DFA state.
            compilationState.DfaStateToRegularVector
            |> Map.find finalDfaStateId
            // Determine which lexer rules are accepted by this regular vector.
            |> RegularVector.acceptingElements
            // Map the indices of the patterns in the regular vector back to their
            // original RuleClauseIndex (it can be different if there are EOF-accepting
            // clauses defined within the same rule).
            |> Set.map (Array.get patternIndices))

    (* TODO :   Add code here to generate warnings about overlapping rules. *)

    /// Maps final (accepting) DFA states to the rule clause they accept.
    let clauseAcceptedByDfaState =
        clausesAcceptedByDfaState
        // Disambiguate overlapping patterns by choosing the rule-clause with the
        // lowest index -- i.e., the rule which was declared earliest in the lexer definition.
        |> Map.map (fun _ -> Set.minElement)

    // Create a LexerRuleDfa record from the compiled DFA.
    {   Transitions = compilationState.Transitions;
        RuleClauseAcceptedByState = clauseAcceptedByDfaState;
        InitialState = initialDfaStateId; }

//
let private preprocessMacro ((macroIdPosition : (SourcePosition * SourcePosition) option, macroId), pattern) (options : CompilationOptions) (macroEnv, badMacros) =
    //
    // OPTIMIZE : Modify this function to use a LazyList to hold the errors
    // instead of an F# list to avoid the list concatenation overhead.
    // OPTIMIZE : Simplify this function using the Cps.choice workflow from ExtCore.
    let rec preprocessMacro pattern cont =
        match pattern with
        | Pattern.Epsilon ->
            Choice1Of2 Regex.Epsilon

        | Pattern.Star r ->
            preprocessMacro r <| fun rResult ->
                match rResult with
                | (Choice2Of2 _ as err) -> err
                | Choice1Of2 r ->
                    Regex.Star r
                    |> Choice1Of2
                |> cont

        | Pattern.Concat (r, s) ->
            preprocessMacro r <| fun rResult ->
            preprocessMacro s <| fun sResult ->
                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    Choice2Of2 (rErrors @ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    err
                | Choice1Of2 r, Choice1Of2 s ->
                    Regex.Concat (r, s)
                    |> Choice1Of2
                |> cont

        | Pattern.And (r, s) ->
            preprocessMacro r <| fun rResult ->
            preprocessMacro s <| fun sResult ->
                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    Choice2Of2 (rErrors @ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    err
                | Choice1Of2 r, Choice1Of2 s ->
                    Regex.And (r, s)
                    |> Choice1Of2
                |> cont

        | Pattern.Or (r, s) ->
            preprocessMacro r <| fun rResult ->
            preprocessMacro s <| fun sResult ->
                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    Choice2Of2 (rErrors @ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    err
                | Choice1Of2 r, Choice1Of2 s ->
                    Regex.Or (r, s)
                    |> Choice1Of2
                |> cont

        (*  Extended patterns are rewritten using the cases of Pattern
            which have corresponding cases in Regex. *)
        | Pattern.OneOrMore r ->
            // Rewrite r+ as rr*
            let rewritten =
                Pattern.Concat (r, Pattern.Star r)

            // Process the rewritten expression.
            preprocessMacro rewritten cont

        | Pattern.Optional r ->
            // Rewrite r? as (|r)
            let rewritten =
                Pattern.Concat (Pattern.Epsilon, r)

            // Process the rewritten expression.
            preprocessMacro rewritten cont

        | Pattern.Repetition (r, atLeast, atMost) ->
            match atLeast, atMost with
            | None, None ->
                ["Invalid number of repetitions. Either the minimum or maximum (or both) number of repetitions must be specified."]
                |> Choice2Of2
                |> cont

            | None, Some atMost ->
                // TODO : If 'atMost' = 0, emit a warning (not an error) message
                // to let the user know the pattern will _always_ be matched.

                /// Repeats the pattern at most the specified number of times.
                let rewritten = Pattern.repeatAtMost atMost r

                // Process the rewritten expression.
                preprocessMacro rewritten cont

            | Some atLeast, None ->
                /// Repeats the pattern at least the specified number of times.
                let rewritten = Pattern.repeatAtLeast atLeast r

                // Process the rewritten expression.
                preprocessMacro rewritten cont

            | Some atLeast, Some atMost
                when atLeast > atMost ->
                ["Invalid number of repetitions. The lower value of the range is greater than the upper value of the range."]
                |> Choice2Of2
                |> cont

            | Some atLeast, Some atMost ->
                /// Repeats the pattern at least 'atLeast' times and at most 'atMost' times.
                let rewritten = Pattern.repeat atLeast atMost r

                // Process the rewritten expression.
                preprocessMacro rewritten cont

        | Pattern.Negate r ->
            preprocessMacro r <| fun rResult ->
                match rResult with
                | (Choice2Of2 _ as err) -> err
                | Choice1Of2 r ->
                    Regex.Negate r
                    |> Choice1Of2
                |> cont

        (* Macro patterns *)
        | Pattern.Macro nestedMacroId ->
            // Make sure this macro doesn't call itself -- macros cannot be recursive.
            // NOTE : This could be handled by checking to see if this macro is already defined
            // because we don't add macros to 'macroEnv' until they're successfully preprocessed;
            // however, this separate check allows us to provide a more specific error message.
            if macroId = nestedMacroId then
                ["Recursive macro definitions are not allowed."]
                |> Choice2Of2
                |> cont
            else
                match Map.tryFind nestedMacroId macroEnv with
                | None ->
                    // Check the 'bad macros' set to avoid returning an error message
                    // for this pattern when the referenced macro contains an error.
                    if Set.contains nestedMacroId badMacros then
                        // We have to return something, so return Empty to take the place
                        // of this macro reference.
                        Choice1Of2 Regex.empty
                        |> cont
                    else
                        Choice2Of2 [ sprintf "The macro '%s' is not defined." nestedMacroId ]
                        |> cont
                | Some nestedMacro ->
                    // Return the pattern for the nested macro so it'll be "inlined" into this pattern.
                    Choice1Of2 nestedMacro
                    |> cont

        (* Characters and character sets *)
        | Pattern.Empty ->
            Regex.empty
            |> Choice1Of2
            |> cont

        | Pattern.Character c ->
            // Make sure the character is an ASCII character unless the 'Unicode' option is set.
            if options.Unicode || int c <= 255 then
                Regex.ofChar c
                |> Choice1Of2
                |> cont
            else
                ["Unicode characters may not be used in patterns unless the 'Unicode' compiler option is set."]
                |> Choice2Of2
                |> cont

        | Pattern.CharacterSet charSet ->
            // Make sure all of the characters in the set are ASCII characters unless the 'Unicode' option is set.
            if options.Unicode || CharSet.forall (fun c -> int c <= 255) charSet then
                Regex.CharacterSet charSet
                |> Choice1Of2
                |> cont
            else
                ["Unicode characters may not be used in patterns unless the 'Unicode' compiler option is set."]
                |> Choice2Of2
                |> cont

        | Pattern.UnicodeCategory abbrev ->
            if options.Unicode then
                match UnicodeCharSet.ofAbbreviation abbrev with
                | None ->
                    [ sprintf "Unknown or invalid Unicode category specified. (Category = %s)" abbrev ]
                    |> Choice2Of2
                    |> cont
                | Some categoryCharSet ->
                    categoryCharSet
                    |> Regex.CharacterSet
                    |> Choice1Of2
                    |> cont
            else
                ["Unicode category patterns may not be used unless the 'Unicode' compiler option is set."]
                |> Choice2Of2
                |> cont

        (* Wildcard pattern *)
        | Pattern.Any ->
            // Macros are not allowed to use the wildcard pattern.
            ["The wildcard pattern cannot be used within macro definitions."]
            |> Choice2Of2
            |> cont

    /// Contains an error if a macro has already been defined with this name; otherwise, None.
    let duplicateNameError =
        if Map.containsKey macroId macroEnv then
            Some <| sprintf "Duplicate macro name '%s'." macroId
        else None

    // Call the function which traverses the macro pattern to validate/preprocess it.
    preprocessMacro pattern <| function
        | Choice2Of2 errors ->
            let errors =
                match duplicateNameError with
                | None -> errors
                | Some duplicateNameError ->
                    duplicateNameError :: errors

            List.rev errors
            |> List.toArray
            |> Choice2Of2

        | Choice1Of2 processedPattern ->
            // If the duplicate name error was set, return it;
            // otherwise there are no errors, so return the processed pattern.
            match duplicateNameError with
            | Some duplicateNameError ->
                [| duplicateNameError |]
                |> Choice2Of2
            | None ->
                Choice1Of2 processedPattern

/// Pre-processes a list of macros from a lexer specification.
/// The macros are validated to verify correct usage, then macro
/// expansion is performed to remove any nested macros.
let private preprocessMacros macros options =
    /// Recursively processes the list of macros.
    let rec preprocessMacros macros errors (macroEnv, badMacros) =
        match macros with
        | [] ->
            // If there are any errors, return them; otherwise,
            // return the map containing the expanded macros.
            match errors with
            | [| |] ->
                assert (Set.isEmpty badMacros)
                Choice1Of2 macroEnv
            | errors ->
                Choice2Of2 (macroEnv, badMacros, errors)

        | ((_, macroId), _ as macro) :: macros ->
            // Validate/process this macro.
            match preprocessMacro macro options (macroEnv, badMacros) with
            | Choice2Of2 macroErrors ->
                // Add this macro's identifier to the set of bad macros.
                let badMacros = Set.add macroId badMacros

                // Append the error messages to the existing error messages.
                let errors = Array.append errors macroErrors

                // Process the remaining macros.
                preprocessMacros macros errors (macroEnv, badMacros)

            | Choice1Of2 preprocessedMacroPattern ->
                // Add the processed macro pattern to the processed macro map.
                let macroEnv = Map.add macroId preprocessedMacroPattern macroEnv

                // Process the remaining macros.
                preprocessMacros macros errors (macroEnv, badMacros)

    // Reverse the macro list so the macros will be processed in
    // top-to-bottom order (i.e., as they were in the lexer
    // definition), then call the preprocessor function.
    preprocessMacros (List.rev macros) Array.empty (Map.empty, Set.empty)

//
let private validateAndSimplifyPattern pattern (macroEnv, badMacros, options) =
    //
    // OPTIMIZE : Modify this function to use a LazyList to hold the errors
    // instead of an F# list to avoid the list concatenation overhead.
    // OPTIMIZE : Simplify this function using the Cps.choice workflow from ExtCore.
    let rec validateAndSimplify pattern cont =
        match pattern with
        | Pattern.Epsilon ->
            Choice1Of2 Regex.Epsilon
            |> cont

        | Pattern.CharacterSet charSet ->
            // Make sure all of the characters in the set are ASCII characters unless the 'Unicode' option is set.
            if options.Unicode || CharSet.forall (fun c -> int c <= int System.Byte.MaxValue) charSet then
                Regex.CharacterSet charSet
                |> Choice1Of2
                |> cont
            else
                ["Unicode characters may not be used in patterns unless the 'Unicode' compiler option is set."]
                |> Choice2Of2
                |> cont

        | Pattern.Macro macroId ->
            match Map.tryFind macroId macroEnv with
            | None ->
                // Check the 'bad macros' set to avoid returning an error message
                // for this pattern when the referenced macro contains an error.
                if Set.contains macroId badMacros then
                    // We have to return something, so return Empty to
                    // take the place of this macro reference.
                    Choice1Of2 Regex.empty
                    |> cont
                else
                    Choice2Of2 [ sprintf "The macro '%s' is not defined." macroId ]
                    |> cont
            | Some nestedMacro ->
                // Return the pattern for the nested macro so it'll be "inlined" into this pattern.
                Choice1Of2 nestedMacro
                |> cont

        | Pattern.UnicodeCategory abbrev ->
            if options.Unicode then
                // Return the CharSet representing this UnicodeCategory.
                match UnicodeCharSet.ofAbbreviation abbrev with
                | None ->
                    [ sprintf "Unknown or invalid Unicode category specified. (Category = %s)" abbrev ]
                    |> Choice2Of2
                    |> cont
                | Some charSet ->
                    Regex.CharacterSet charSet
                    |> Choice1Of2
                    |> cont
            else
                ["Unicode category patterns may not be used unless the 'Unicode' compiler option is set."]
                |> Choice2Of2
                |> cont

        | Pattern.Negate r ->
            validateAndSimplify r <| fun rResult ->
                match rResult with
                | (Choice2Of2 _ as err) -> err
                | Choice1Of2 r ->
                    Regex.Negate r
                    |> Choice1Of2
                |> cont

        | Pattern.Star r ->
            validateAndSimplify r <| fun rResult ->
                match rResult with
                | (Choice2Of2 _ as err) -> err
                | Choice1Of2 r ->
                    Regex.Star r
                    |> Choice1Of2
                |> cont

        | Pattern.Concat (r, s) ->
            validateAndSimplify r <| fun rResult ->
            validateAndSimplify s <| fun sResult ->
                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    Choice2Of2 (rErrors @ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    err
                | Choice1Of2 r, Choice1Of2 s ->
                    Regex.Concat (r, s)
                    |> Choice1Of2
                |> cont

        | Pattern.And (r, s) ->
            validateAndSimplify r <| fun rResult ->
            validateAndSimplify s <| fun sResult ->
                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    Choice2Of2 (rErrors @ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    err
                | Choice1Of2 r, Choice1Of2 s ->
                    Regex.And (r, s)
                    |> Choice1Of2
                |> cont

        | Pattern.Or (r, s) ->
            validateAndSimplify r <| fun rResult ->
            validateAndSimplify s <| fun sResult ->
                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    Choice2Of2 (rErrors @ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    err
                | Choice1Of2 r, Choice1Of2 s ->
                    Regex.Or (r, s)
                    |> Choice1Of2
                |> cont

        (*  Extended patterns are rewritten using the cases of Pattern
            which have corresponding cases in Regex. *)
        | Pattern.Empty ->
            Regex.empty
            |> Choice1Of2
            |> cont
        
        | Pattern.Any ->
            Choice1Of2 Regex.Any
            |> cont

        | Pattern.Character c ->
            // Make sure the character is an ASCII character unless the 'Unicode' option is set.
            if options.Unicode || int c <= 255 then
                Regex.ofChar c
                |> Choice1Of2
                |> cont
            else
                ["Unicode characters may not be used in patterns unless the 'Unicode' compiler option is set."]
                |> Choice2Of2
                |> cont

        | Pattern.OneOrMore r ->
            // Rewrite r+ as rr*
            let rewritten =
                Pattern.Concat (r, Pattern.Star r)

            // Process the rewritten expression.
            validateAndSimplify rewritten cont

        | Pattern.Optional r ->
            // Rewrite r? as (|r)
            let rewritten =
                Pattern.Or (Pattern.Epsilon, r)

            // Process the rewritten expression.
            validateAndSimplify rewritten cont

        | Pattern.Repetition (r, atLeast, atMost) ->
            match atLeast, atMost with
            | None, None ->
                ["Invalid number of repetitions. Either the minimum or maximum (or both) number of repetitions must be specified."]
                |> Choice2Of2
                |> cont

            | None, Some atMost ->
                // TODO : If 'atMost' = 0, emit a warning (not an error) message
                // to let the user know the pattern will _always_ be matched.

                /// Repeats the pattern at most the specified number of times.
                let rewritten = Pattern.repeatAtMost atMost r

                // Process the rewritten expression.
                validateAndSimplify rewritten cont

            | Some atLeast, None ->
                /// Repeats the pattern at least the specified number of times.
                let rewritten = Pattern.repeatAtLeast atLeast r

                // Process the rewritten expression.
                validateAndSimplify rewritten cont

            | Some atLeast, Some atMost
                when atLeast > atMost ->
                ["Invalid number of repetitions. The lower value of the range is greater than the upper value of the range."]
                |> Choice2Of2
                |> cont

            | Some atLeast, Some atMost ->
                /// Repeats the pattern at least 'atLeast' times and at most 'atMost' times.
                let rewritten = Pattern.repeat atLeast atMost r

                // Process the rewritten expression.
                validateAndSimplify rewritten cont

    // Call the function which traverses the pattern to validate/preprocess it.
    validateAndSimplify pattern <| function
        | Choice2Of2 errors ->
            List.rev errors
            |> List.toArray
            |> Choice2Of2
        | Choice1Of2 processedPattern ->
            Choice1Of2 processedPattern

//
let private getAlphabet regex =
    let rec getAlphabet regex =
        cont {
        match regex with
        | Regex.Any
        | Regex.Epsilon ->
            return CharSet.empty

        | Regex.CharacterSet charSet ->
            return charSet

        | Regex.Negate r
        | Regex.Star r ->
            return! getAlphabet r

        | Regex.And (r, s)
        | Regex.Concat (r, s)
        | Regex.Or (r, s) ->
            let! rAlphabet = getAlphabet r
            let! sAlphabet = getAlphabet s
            return CharSet.union rAlphabet sAlphabet
        }

    getAlphabet regex id

// This is necessary for fslex-compatibility.
// In the future, it will be moved into the fslex-compatibility backend.
let private rewriteNegatedCharSets universe regex =
    let rec rewriteNegatedCharSets regex =
        cont {
        match regex with
        | Regex.Negate (Regex.CharacterSet charSet) ->
            return
                charSet
                |> CharSet.difference universe
                |> Regex.CharacterSet

        | Regex.Any
        | Regex.Epsilon
        | Regex.CharacterSet _
            as regex ->
            return regex

        | Regex.Negate r ->
            let! r = rewriteNegatedCharSets r
            return Regex.Negate r

        | Regex.Star r ->
            let! r = rewriteNegatedCharSets r
            return Regex.Star r

        | Regex.And (r, s) ->
            let! r = rewriteNegatedCharSets r
            let! s = rewriteNegatedCharSets s
            return Regex.And (r, s)

        | Regex.Concat (r, s) ->
            let! r = rewriteNegatedCharSets r
            let! s = rewriteNegatedCharSets s
            return Regex.Concat (r, s)

        | Regex.Or (r, s) ->
            let! r = rewriteNegatedCharSets r
            let! s = rewriteNegatedCharSets s
            return Regex.Or (r, s)
        }

    rewriteNegatedCharSets regex id

//
let private compileRule (rule : Rule) (options : CompilationOptions) (macroEnv, badMacros) =
    (* TODO :   Simplify this function by folding over rule.Clauses; this way,
                we don't create so many intermediate data structures and we avoid
                the need to split the clauses based on which RuleClausePattern
                they're defined with. *)

    let ruleClauses =
        // The clauses are provided in reverse order from the way they're
        // specified in the lexer definition, so reverse them to put them
        // in the correct order.
        // NOTE : The ordering only matters when two or more clauses overlap,
        // because then the ordering is used to decide which action to execute.
        rule.Clauses
        |> List.rev
        |> List.toArray

    // Extract any clauses which match the end-of-file pattern;
    // these are handled separately from the other patterns.
    let patterns, eofClauseIndices =
        // TODO : Simplify the code below using the splitter function from ExtCore.

        let ruleClauseCount = Array.length ruleClauses
        
        let patterns = ResizeArray<_> (Array.length ruleClauses)
        let mutable eofClauseIndices = Set.empty

        // Extract the relevant information from the pattern of each clause,
        // based on which case of RuleClausePattern they're defined with.
        for i = 0 to ruleClauseCount - 1 do
            let clause = ruleClauses.[i]
            match clause.Pattern with
            | Pattern pattern ->
                patterns.Add (
                    (Int32WithMeasure i : RuleClauseIndex),
                    pattern)
            | EndOfFile ->
                eofClauseIndices <-
                    Set.add (Int32WithMeasure i : RuleClauseIndex) eofClauseIndices

        // Return the data.
        patterns.ToArray (),
        eofClauseIndices

    /// The index of the rule clause whose action will be executed
    /// if the lexer attempts to match this rule once the end-of-file
    /// has been reached.
    let eofAcceptingClauseIndex =
        if Set.isEmpty eofClauseIndices then
            None
        else
            // Only the earliest use of the "eof" pattern will be matched.
            let acceptingClauseIndex = Set.minElement eofClauseIndices
            let neverMatchedClauseIndices = Set.remove acceptingClauseIndex eofClauseIndices

            // TODO : Implement code to emit warning messages when 'neverMatchedClauseIndices'
            // is non-empty. (E.g., "This pattern will never be matched.")
//            if not <| Set.isEmpty neverMatchedClauseIndices then
//                // TODO
//                ()

            Some acceptingClauseIndex

    /// The index of the wildcard rule clause, if this rule contains one.
    let wildcardAcceptingClauseIndex =
        let wildcardClauseIndices =
            patterns
            |> Array.choose (fun (idx, pat) ->
                match pat with
                | Any -> Some idx
                | _ -> None)
            |> Set.ofArray

        if Set.isEmpty wildcardClauseIndices then
            None
        else
            // Only the earliest use of the wildcard pattern will be matched.
            let acceptingClauseIndex = Set.minElement wildcardClauseIndices
            let neverMatchedClauseIndices = Set.remove acceptingClauseIndex wildcardClauseIndices

            // TODO : Implement code to emit warning messages when 'neverMatchedClauseIndices'
            // is non-empty. (E.g., "This pattern will never be matched.")
//            if not <| Set.isEmpty neverMatchedClauseIndices then
//                // TODO
//                ()

            Some acceptingClauseIndex

    choice {
    // Validate and simplify the patterns of the rule clauses.
    let! ruleClauseRegexes =
        let simplifiedRuleClausePatterns =
            patterns
            |> Array.map (fun (originalRuleClauseIndex, pattern) ->
                // TODO : Simplify using Choice.Result.map
                match validateAndSimplifyPattern pattern (macroEnv, badMacros, options) with
                | Choice2Of2 errors ->
                    Choice2Of2 errors
                | Choice1Of2 pattern ->
                    Choice1Of2 (originalRuleClauseIndex, pattern))

        // Put all of the "results" in one array and all of the "errors" in another.
        let results = ResizeArray<_> (Array.length simplifiedRuleClausePatterns)
        let errors = ResizeArray<_> (Array.length simplifiedRuleClausePatterns)
        simplifiedRuleClausePatterns
        |> Array.iter (function
            | Choice2Of2 errorArr ->
                errors.AddRange errorArr
            | Choice1Of2 result ->
                results.Add result)

        // If there are any errors, return them; otherwise, return the results.
        if errors.Count > 0 then
            Choice2Of2 <| errors.ToArray ()
        else
            Choice1Of2 <| results.ToArray ()

    /// The DFA compiled from the rule clause patterns.
    let compiledPatternDfa =
        let regexOriginalClauseIndices, ruleClauseRegexes =
            Array.unzip ruleClauseRegexes
            
        (* TEMP :   For compatibility with fslex, we need to determine the alphabet used
                    by the rule, then rewrite any negated character sets so the transition
                    table is generated in a way that fslex can handle. *)
        let ruleAlphabet =
            ruleClauseRegexes
            |> Array.map getAlphabet
            |> Array.reduce CharSet.union
            // Add the low ASCII characters too, like fslex does.
            |> CharSet.union (CharSet.ofRange (char 0) (char 127))

        // Rewrite the regexes so they don't contain negated character sets.
        let ruleClauseRegexes =
            ruleClauseRegexes
            |> Array.map (rewriteNegatedCharSets ruleAlphabet)

        rulePatternsToDfa ruleClauseRegexes regexOriginalClauseIndices options

    // If this rule has a pattern accepting the end-of-file marker,
    // create an additional DFA state to serve as the EOF-accepting state
    // and create a transition edge labeled with the EOF symbol to it.
    let compiledPatternDfa =
        match eofAcceptingClauseIndex with
        | None ->
            compiledPatternDfa
        | Some eofAcceptingClauseIndex ->
            let eofAcceptingState, transitions =
                LexerDfaGraph.createVertex compiledPatternDfa.Transitions
            let transitions =
                LexerDfaGraph.addEofEdge compiledPatternDfa.InitialState eofAcceptingState transitions
            { compiledPatternDfa with
                Transitions = transitions;
                RuleClauseAcceptedByState =
                    compiledPatternDfa.RuleClauseAcceptedByState
                    |> Map.add eofAcceptingState eofAcceptingClauseIndex; }

    // If this rule has a clause with the wildcard pattern, create an additional
    // DFA state which accepts any single character which won't be matched by the
    // earlier patterns in the rule.
    let compiledPatternDfa =
        match wildcardAcceptingClauseIndex with
        | None ->
            compiledPatternDfa
        | Some wildcardAcceptingClauseIndex ->
            // TEMP : The way the transition characters are computed here is specific
            // to fslex -- once we implement our own interpreter, we'll have to come
            // up with a backend-specific way to handle this. Perhaps we can just store
            // the wildcard-clause index in the returned DFA, and let the plugins themselves
            // compute the transition characters.

            /// The alphabet for this rule.
            let ruleAlphabet =
                // The alphabet for this rule is the edge-label-set of the transition graph.
                (CharSet.empty, compiledPatternDfa.Transitions.AdjacencyMap)
                ||> Map.fold (fun ruleAlphabet _ edgeChars ->
                    CharSet.union ruleAlphabet edgeChars)

            /// The set of characters labelling the out-edges of the initial DFA state.
            let initialEdgeLabels =
                (CharSet.empty, compiledPatternDfa.Transitions.AdjacencyMap)
                ||> Map.fold (fun initialEdgeLabels edgeKey edgeChars ->
                    // We only care about out-edges from the initial DFA state.
                    if edgeKey.Source = compiledPatternDfa.InitialState then
                        CharSet.union initialEdgeLabels edgeChars
                    else
                        initialEdgeLabels)

            /// The characters matched by this rule's wildcard pattern.
            let wildcardChars =
                // Augment the rule alphabet with the low ASCII characters,
                // because that's how fslex does it and we need to be compatible (for now).
                let ruleAlphabet =
                    CharSet.ofRange (char 0) (char 127)
                    |> CharSet.union ruleAlphabet

                CharSet.difference ruleAlphabet initialEdgeLabels

            // If the set of characters matched by the wildcard pattern is not empty,
            // create a new DFA state which accepts the wildcard pattern, then add
            // transition edges to it from the initial state.
            if CharSet.isEmpty wildcardChars then
                // TODO : Emit a warning to let the user know this pattern will never be matched.
                Debug.WriteLine "Warning: Wildcard pattern in rule will never be matched."

                compiledPatternDfa
            else
                let wildcardAcceptingState, transitions =
                    LexerDfaGraph.createVertex compiledPatternDfa.Transitions
                let transitions =
                    LexerDfaGraph.addEdges compiledPatternDfa.InitialState wildcardAcceptingState wildcardChars transitions

                { compiledPatternDfa with
                    Transitions = transitions;
                    RuleClauseAcceptedByState =
                        compiledPatternDfa.RuleClauseAcceptedByState
                        |> Map.add wildcardAcceptingState wildcardAcceptingClauseIndex; }

    // TODO : Emit warnings about any overlapping patterns.
    // E.g., "This pattern will never be matched."

    // Create a CompiledRule record from the compiled DFA.
    return {
        Dfa = compiledPatternDfa;
        Parameters =
            // Reverse the list so it's in the correct left-to-right order.
            List.rev rule.Parameters
            |> List.toArray;
        RuleClauseActions =
            ruleClauses
            |> Array.map (fun clause ->
                clause.Action); }
    }


/// A compiled lexer specification.
type CompiledSpecification = {
    //
    Header : CodeFragment option;
    //
    Footer : CodeFragment option;
    //
    CompiledRules : Map<RuleIdentifier, CompiledRule>;
//    //
//    StartRule : RuleIdentifier;
}

/// Creates pattern-matching DFAs from the lexer rules.
let lexerSpec (spec : Specification) options =
    // Validate and simplify the macros to create the macro table/environment.
    match preprocessMacros spec.Macros options with
    | Choice2Of2 (macroEnv, badMacros, errors) ->
        // TODO : Validate the rule clauses, but don't compile the rule DFAs.
        // This way we can return all applicable errors instead of just those for the macros.
        Choice2Of2 errors
    | Choice1Of2 macroEnv ->
        (* Compile the lexer rules *)
        (* TODO :   Simplify the code below using monadic operators. *)
        let ruleIdentifiers, rules =
            let ruleCount = List.length spec.Rules
            let ruleIdentifiers = Array.zeroCreate ruleCount
            let rules = Array.zeroCreate ruleCount

            // TODO : Check for duplicate rule identifiers
            (ruleCount - 1, spec.Rules)
            ||> List.fold (fun index (ruleId, rule) ->
                ruleIdentifiers.[index] <- ruleId
                rules.[index] <- rule
                index - 1)
            |> ignore

            ruleIdentifiers, rules

        let compiledRules, compilationErrors =
            rules
            |> Array.mapPartition (fun rule ->
                compileRule rule options (macroEnv, Set.empty))

        // If there are errors, return them; otherwise, create a
        // CompiledSpecification record from the compiled rules.
        if Array.isEmpty compilationErrors then
            Choice1Of2 {
                Header = spec.Header;
                Footer = spec.Footer;
                CompiledRules =
                    (Map.empty, ruleIdentifiers, compiledRules)
                    |||> Array.fold2 (fun map (_, ruleId) compiledRule ->
                        Map.add ruleId compiledRule map); }
        else
            Choice2Of2 <| Array.concat compilationErrors

