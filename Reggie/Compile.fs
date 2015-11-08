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

namespace Reggie.Compile

open System.Diagnostics
open LanguagePrimitives
open ExtCore.Control
open ExtCore.Control.Cps
open Reggie
open Reggie.SpecializedCollections
open Reggie.Graph
open Reggie.Ast


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

    // OPTIMIZE : Use the TagBimap type from ExtCore to combine these
    //            next two fields into a single field.
    /// Maps a DFA state to the regular vector it represents (and vice versa).
    //DfaStateToRegularVector : TagBimap<DfaState, RegularVector>;

    /// Maps regular vectors to the DFA state representing them.
    RegularVectorToDfaState : HashMap<RegularVector, DfaStateId>;
    /// Maps a DFA state to the regular vector it represents.
    DfaStateToRegularVector : TagMap<DfaState, RegularVector>;

    /// Caches used for memoizing computations.
    Cache : CompilationCache;
}

/// Functional operators related to the CompilationState record.
/// These operators are designed to adhere to either the Reader or State monads.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private CompilationState =
    /// Empty compilation state.
    let empty = {
        Transitions = LexerDfaGraph.Empty;
        FinalStates = Set.empty;
        RegularVectorToDfaState = HashMap.empty;
        DfaStateToRegularVector = TagMap.empty;
        Cache = CompilationCache.empty; }

    //
    let inline tryGetDfaState regVec (compilationState : CompilationState) =
        HashMap.tryFind regVec compilationState.RegularVectorToDfaState

    //
    let inline getRegularVector dfaState (compilationState : CompilationState) =
        TagMap.find dfaState compilationState.DfaStateToRegularVector

    //
    let createDfaState regVec (compilationState : CompilationState) =
        // Preconditions
        // TODO

        Debug.Assert (
            not <| HashMap.containsKey regVec compilationState.RegularVectorToDfaState,
            "The compilation state already contains a DFA state for this regular vector.")

        /// The DFA state representing this regular vector.
        let (dfaState : DfaStateId), transitions =
            compilationState.Transitions.CreateVertex ()

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
                    HashMap.add regVec dfaState compilationState.RegularVectorToDfaState;
                DfaStateToRegularVector =
                    TagMap.add dfaState regVec compilationState.DfaStateToRegularVector;
                 }

        // Return the new DFA state and the updated compilation state.
        dfaState, compilationState


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
    RuleClauseActions : PositionedValue<CodeFragment>[];
}

/// A compiled lexer specification.
type CompiledSpecification = {
    //
    Header : PositionedValue<CodeFragment> option;
    //
    Footer : PositionedValue<CodeFragment> option;
    //
    CompiledRules : Map<RuleIdentifier, CompiledRule>;
}


//
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Compiler =
    //
    let private transitions regularVector derivativeClass (transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState) =
        // Preconditions
        if CharSet.isEmpty derivativeClass then
            invalidArg "derivativeClass" "The derivative class is an empty set."

        // The derivative of the regular vector w.r.t. the chosen element.
        let regularVector', compilationState =
            // Compute the derivative of the regular vector
            let regularVector', compilationCache =
                // Choose an element from the derivative class; any element
                // will do (which is the point behind the derivative classes).
                let derivativeClassElement = CharSet.minElement derivativeClass
                RegularVector.derivative derivativeClassElement regularVector compilationState.Cache
            
            // Return the derivative vector and the updated compilation state.
            regularVector', { compilationState with Cache = compilationCache; }

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
                match CompilationState.tryGetDfaState regularVector' compilationState with
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
                        TagSet.add newDfaState unvisitedTransitionTargets

                    newDfaState,
                    unvisitedTransitionTargets,
                    compilationState

            //
            let transitionsFromCurrentDfaState =
                HashMap.add derivativeClass targetDfaState transitionsFromCurrentDfaState

            transitionsFromCurrentDfaState,
            unvisitedTransitionTargets,
            compilationState

    // TODO : Re-write this using the readerState workflow.
    let rec private createDfa pending compilationState =
        // If there are no more pending states, we're finished compiling.
        if TagSet.isEmpty pending then
            compilationState
        else
            //
            let currentState = TagSet.minElement pending
            let pending = TagSet.remove currentState pending

            //
            let regularVector = CompilationState.getRegularVector currentState compilationState

            // If this regular vector represents the error state, there's nothing to do
            // for it -- just continue processing the worklist.
            if RegularVector.isEmpty regularVector then
                createDfa pending compilationState
            else
                /// The approximate set of derivative classes of the regular vector,
                /// representing transitions out of the DFA state representing it.
                let derivativeClasses, compilationState =
                    let derivativeClasses, compilationCache =
                        RegularVector.derivativeClasses regularVector compilationState.Cache
                
                    derivativeClasses, { compilationState with Cache = compilationCache; }

                // For each DFA state (regular vector) targeted by a transition (derivative class),
                // add the DFA state to the compilation state (if necessary), then add an edge
                // to the transition graph from this DFA state to the target DFA state.
                let transitionsFromCurrentDfaState, unvisitedTransitionTargets, compilationState =
                    ((HashMap.empty, TagSet.empty, compilationState), derivativeClasses)
                    ||> HashSet.fold (fun state derivativeClass ->
                        if CharSet.isEmpty derivativeClass then state
                        else transitions regularVector derivativeClass state)

                // Add any newly-created, unvisited states to the
                // set of states which still need to be visited.
                let pending = TagSet.union pending unvisitedTransitionTargets

                let compilationState =
                    { compilationState with
                        Transitions =
                            // Add the unvisited transition targets to the transition graph.
                            (compilationState.Transitions, transitionsFromCurrentDfaState)
                            ||> HashMap.fold (fun transitions derivativeClass target ->
                                transitions.AddEdges currentState target derivativeClass); }

                // Continue processing recursively.
                createDfa pending compilationState

    //
    let private rulePatternsToDfa (rulePatterns : RegularVector) (patternIndices : RuleClauseIndex[]) : LexerRuleDfa =
        // Preconditions
        if Array.isEmpty rulePatterns then
            invalidArg "rulePatterns" "The rule must contain at least one (1) pattern."
        elif Array.length rulePatterns <> Array.length patternIndices then
            invalidArg "patternIndices" "The array must have the same length as 'rulePatterns'."

        // The initial DFA compilation state.
        let initialDfaStateId, compilationState =
            CompilationState.empty
            |> CompilationState.createDfaState rulePatterns

        // Compile the DFA.
        let compilationState =
            let initialPending = TagSet.singleton initialDfaStateId
            createDfa initialPending compilationState

        //
        let clausesAcceptedByDfaState =
            compilationState.FinalStates
            |> Map.ofKeys (fun finalDfaStateId ->
                // Get the regular vector represented by this DFA state.
                compilationState.DfaStateToRegularVector
                |> TagMap.find finalDfaStateId
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
    let private preprocessMacro ({ Value = macroId; PositionRange = _; }, pattern) (options : CompilationOptions) (macroEnv, badMacros) =
        //
        let rec preprocessMacro pattern =
            cont {
            match pattern with
            | Pattern.Epsilon ->
                return Choice1Of2 Regex.epsilon

            | Pattern.Star r ->
                let! rResult = preprocessMacro r
                match rResult with
                | Choice2Of2 _ as err ->
                    return err
                | Choice1Of2 r ->
                    return
                        Regex.star r
                        |> Choice1Of2

            | Pattern.Concat (r, s) ->
                let! rResult = preprocessMacro r
                let! sResult = preprocessMacro s

                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    return Choice2Of2 (rErrors ++ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    return err
                | Choice1Of2 r, Choice1Of2 s ->
                    return
                        Regex.concat r s
                        |> Choice1Of2

            | Pattern.And (r, s) ->
                let! rResult = preprocessMacro r
                let! sResult = preprocessMacro s

                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    return Choice2Of2 (rErrors ++ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    return err
                | Choice1Of2 r, Choice1Of2 s ->
                    return
                        Regex.andr r s
                        |> Choice1Of2

            | Pattern.Or (r, s) ->
                let! rResult = preprocessMacro r
                let! sResult = preprocessMacro s

                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    return Choice2Of2 (rErrors ++ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    return err
                | Choice1Of2 r, Choice1Of2 s ->
                    return
                        Regex.orr r s
                        |> Choice1Of2

            | Pattern.Xor (r, s) ->
                let! rResult = preprocessMacro r
                let! sResult = preprocessMacro s

                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    return Choice2Of2 (rErrors ++ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    return err
                | Choice1Of2 r, Choice1Of2 s ->
                    return
                        // The Xor pattern is implemented using the following identity:
                        //   p XOR q => (p OR q) AND (NOT (p AND q))
                        Regex.andr
                            (Regex.orr r s)
                            (Regex.negate <|
                                Regex.andr r s)
                        |> Choice1Of2

            (*  Extended patterns are rewritten using the cases of Pattern
                which have corresponding cases in Regex. *)
            | Pattern.OneOrMore r ->
                // Rewrite r+ as rr*
                let rewritten =
                    Pattern.Concat (r, Pattern.Star r)

                // Process the rewritten expression.
                return! preprocessMacro rewritten

            | Pattern.Optional r ->
                // Rewrite r? as (|r)
                let rewritten =
                    Pattern.Or (Pattern.Epsilon, r)

                // Process the rewritten expression.
                return! preprocessMacro rewritten

            | Pattern.Repetition (r, atLeast, atMost) ->
                match atLeast, atMost with
                | None, None ->
                    return
                        "Invalid number of repetitions. Either the minimum or maximum (or both) number of repetitions must be specified."
                        |> LazyList.singleton
                        |> Choice2Of2

                | None, Some atMost ->
                    // TODO : If 'atMost' = 0, emit a warning (not an error) message
                    // to let the user know the pattern will _always_ be matched.

                    /// Repeats the pattern at most the specified number of times.
                    let rewritten = Pattern.repeatAtMost atMost r

                    // Process the rewritten expression.
                    return! preprocessMacro rewritten

                | Some atLeast, None ->
                    /// Repeats the pattern at least the specified number of times.
                    let rewritten = Pattern.repeatAtLeast atLeast r

                    // Process the rewritten expression.
                    return! preprocessMacro rewritten

                | Some atLeast, Some atMost
                    when atLeast > atMost ->
                    return
                        "Invalid number of repetitions. The lower value of the range is greater than the upper value of the range."
                        |> LazyList.singleton
                        |> Choice2Of2

                | Some atLeast, Some atMost ->
                    /// Repeats the pattern at least 'atLeast' times and at most 'atMost' times.
                    let rewritten = Pattern.repeat atLeast atMost r

                    // Process the rewritten expression.
                    return! preprocessMacro rewritten

            | Pattern.Negate r ->
                let! rResult = preprocessMacro r

                match rResult with
                | Choice2Of2 _ as err ->
                    return err
                | Choice1Of2 r ->
                    return
                        Regex.negate r
                        |> Choice1Of2

            (* Macro patterns *)
            | Pattern.Macro nestedMacroId ->
                // Make sure this macro doesn't call itself -- macros cannot be recursive.
                // NOTE : This could be handled by checking to see if this macro is already defined
                // because we don't add macros to 'macroEnv' until they're successfully preprocessed;
                // however, this separate check allows us to provide a more specific error message.
                if macroId = nestedMacroId then
                    return
                        "Recursive macro definitions are not allowed."
                        |> LazyList.singleton
                        |> Choice2Of2

                else
                    match Map.tryFind nestedMacroId macroEnv with
                    | None ->
                        // Check the 'bad macros' set to avoid returning an error message
                        // for this pattern when the referenced macro contains an error.
                        if Set.contains nestedMacroId badMacros then
                            // We have to return something, so return Empty to take the place
                            // of this macro reference.
                            return Choice1Of2 Regex.empty
                        else
                            return
                                sprintf "The macro '%s' is not defined." nestedMacroId
                                |> LazyList.singleton
                                |> Choice2Of2

                    | Some nestedMacro ->
                        // Return the pattern for the nested macro so it'll be "inlined" into this pattern.
                        return Choice1Of2 nestedMacro

            (* Characters and character sets *)
            | Pattern.Empty ->
                return
                    Regex.empty
                    |> Choice1Of2

            | Pattern.Character c ->
                // Make sure the character is an ASCII character unless the 'Unicode' option is set.
                if options.Unicode || int c <= 255 then
                    return
                        Regex.ofChar c
                        |> Choice1Of2
                else
                    return
                        "Unicode characters may not be used in patterns unless the 'Unicode' compiler option is set."
                        |> LazyList.singleton
                        |> Choice2Of2

            | Pattern.CharacterSet charSet ->
                // Make sure all of the characters in the set are ASCII characters unless the 'Unicode' option is set.
                if options.Unicode || CharSet.forall (fun c -> int c <= 255) charSet then
                    return
                        Regex.ofCharSet charSet
                        |> Choice1Of2
                else
                    return
                        "Unicode characters may not be used in patterns unless the 'Unicode' compiler option is set."
                        |> LazyList.singleton
                        |> Choice2Of2

            | Pattern.UnicodeCategory abbrev ->
                if options.Unicode then
                    match UnicodeCharSet.ofAbbreviation abbrev with
                    | None ->
                        return
                            sprintf "Unknown or invalid Unicode category specified. (Category = %s)" abbrev
                            |> LazyList.singleton
                            |> Choice2Of2
                    | Some categoryCharSet ->
                        return
                            Regex.ofCharSet categoryCharSet
                            |> Choice1Of2
                else
                    return
                        "Unicode category patterns may not be used unless the 'Unicode' compiler option is set."
                        |> LazyList.singleton
                        |> Choice2Of2

            (* Wildcard pattern *)
            | Pattern.Any ->
                // Macros are not allowed to use the wildcard pattern.
                return
                    "The wildcard pattern cannot be used within macro definitions."
                    |> LazyList.singleton
                    |> Choice2Of2
            }

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
                        LazyList.cons duplicateNameError errors

                LazyList.toArray errors
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

            | ({ Value = macroId; PositionRange = _; }, _ as macro) :: macros ->
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

    /// Determines if all characters in the specified CharSet are ASCII characters;
    /// that is, they can be represented by an 8-bit value.
    let private isAsciiCharSet (charSet : CharSet) : bool =
        CharSet.maxElement charSet <= char System.Byte.MaxValue

    //
    let private validateAndSimplifyPattern pattern (macroEnv, badMacros, options) =
        //
        let rec validateAndSimplify pattern =
            cont {
            match pattern with
            | Pattern.Epsilon ->
                return Choice1Of2 Regex.epsilon

            | Pattern.CharacterSet charSet ->
                // Make sure all of the characters in the set are ASCII characters unless the 'Unicode' option is set.
                if options.Unicode || isAsciiCharSet charSet then
                    return
                        Regex.ofCharSet charSet
                        |> Choice1Of2
                else
                    return
                        "Unicode characters may not be used in patterns unless the 'Unicode' compiler option is set."
                        |> LazyList.singleton
                        |> Choice2Of2

            | Pattern.Macro macroId ->
                match Map.tryFind macroId macroEnv with
                | None ->
                    // Check the 'bad macros' set to avoid returning an error message
                    // for this pattern when the referenced macro contains an error.
                    if Set.contains macroId badMacros then
                        // We have to return something, so return Empty to
                        // take the place of this macro reference.
                        return Choice1Of2 Regex.empty
                    else
                        return
                            sprintf "The macro '%s' is not defined." macroId
                            |> LazyList.singleton
                            |> Choice2Of2
                | Some nestedMacro ->
                    // Return the pattern for the nested macro so it'll be "inlined" into this pattern.
                    return Choice1Of2 nestedMacro

            | Pattern.UnicodeCategory abbrev ->
                if options.Unicode then
                    // Return the CharSet representing this UnicodeCategory.
                    match UnicodeCharSet.ofAbbreviation abbrev with
                    | None ->
                        return
                            sprintf "Unknown or invalid Unicode category specified. (Category = %s)" abbrev
                            |> LazyList.singleton
                            |> Choice2Of2

                    | Some charSet ->
                        return
                            Regex.ofCharSet charSet
                            |> Choice1Of2
                else
                    return
                        "Unicode category patterns may not be used unless the 'Unicode' compiler option is set."
                        |> LazyList.singleton
                        |> Choice2Of2

            | Pattern.Negate r ->
                let! rResult = validateAndSimplify r
            
                match rResult with
                | Choice2Of2 _ as err ->
                    return err
                | Choice1Of2 r ->
                    return
                        Regex.negate r
                        |> Choice1Of2

            | Pattern.Star r ->
                let! rResult = validateAndSimplify r
            
                match rResult with
                | Choice2Of2 _ as err ->
                    return err
                | Choice1Of2 r ->
                    return
                        Regex.star r
                        |> Choice1Of2

            | Pattern.Concat (r, s) ->
                let! rResult = validateAndSimplify r
                let! sResult = validateAndSimplify s

                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    return Choice2Of2 (rErrors ++ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    return err
                | Choice1Of2 r, Choice1Of2 s ->
                    return
                        Regex.concat r s
                        |> Choice1Of2

            | Pattern.And (r, s) ->
                let! rResult = validateAndSimplify r
                let! sResult = validateAndSimplify s

                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    return Choice2Of2 (rErrors ++ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    return err
                | Choice1Of2 r, Choice1Of2 s ->
                    return
                        Regex.andr r s
                        |> Choice1Of2

            | Pattern.Or (r, s) ->
                let! rResult = validateAndSimplify r
                let! sResult = validateAndSimplify s

                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    return Choice2Of2 (rErrors ++ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    return err
                | Choice1Of2 r, Choice1Of2 s ->
                    return
                        Regex.orr r s
                        |> Choice1Of2

            | Pattern.Xor (r, s) ->
                let! rResult = validateAndSimplify r
                let! sResult = validateAndSimplify s

                match rResult, sResult with
                | Choice2Of2 rErrors, Choice2Of2 sErrors ->
                    return Choice2Of2 (rErrors ++ sErrors)
                | (Choice2Of2 _ as err), Choice1Of2 _
                | Choice1Of2 _, (Choice2Of2 _ as err) ->
                    return err
                | Choice1Of2 r, Choice1Of2 s ->
                    return
                        // The Xor pattern is implemented using the following identity:
                        //   p XOR q => (p OR q) AND (NOT (p AND q))
                        Regex.andr
                            (Regex.orr r s)
                            (Regex.negate <|
                                Regex.andr r s)
                        |> Choice1Of2

            (*  Extended patterns are rewritten using the cases of Pattern
                which have corresponding cases in Regex. *)
            | Pattern.Empty ->
                return
                    Regex.empty
                    |> Choice1Of2
        
            | Pattern.Any ->
                return Choice1Of2 (Regex.negate Regex.empty)

            | Pattern.Character c ->
                // Make sure the character is an ASCII character unless the 'Unicode' option is set.
                if options.Unicode || int c <= int System.Byte.MaxValue then
                    return
                        Regex.ofChar c
                        |> Choice1Of2
                else
                    return
                        "Unicode characters may not be used in patterns unless the 'Unicode' compiler option is set."
                        |> LazyList.singleton
                        |> Choice2Of2

            | Pattern.OneOrMore r ->
                // Rewrite r+ as rr*
                let rewritten =
                    Pattern.Concat (r, Pattern.Star r)

                // Process the rewritten expression.
                return! validateAndSimplify rewritten

            | Pattern.Optional r ->
                // Rewrite r? as (|r)
                let rewritten =
                    Pattern.Or (Pattern.Epsilon, r)

                // Process the rewritten expression.
                return! validateAndSimplify rewritten

            | Pattern.Repetition (r, atLeast, atMost) ->
                match atLeast, atMost with
                | None, None ->
                    return
                        "Invalid number of repetitions. Either the minimum or maximum (or both) number of repetitions must be specified."
                        |> LazyList.singleton
                        |> Choice2Of2

                | None, Some atMost ->
                    // TODO : If 'atMost' = 0, emit a warning (not an error) message
                    // to let the user know the pattern will _always_ be matched.

                    /// Repeats the pattern at most the specified number of times.
                    let rewritten = Pattern.repeatAtMost atMost r

                    // Process the rewritten expression.
                    return! validateAndSimplify rewritten

                | Some atLeast, None ->
                    /// Repeats the pattern at least the specified number of times.
                    let rewritten = Pattern.repeatAtLeast atLeast r

                    // Process the rewritten expression.
                    return! validateAndSimplify rewritten

                | Some atLeast, Some atMost
                    when atLeast > atMost ->
                    return
                        "Invalid number of repetitions. The lower value of the range is greater than the upper value of the range."
                        |> LazyList.singleton
                        |> Choice2Of2

                | Some atLeast, Some atMost ->
                    /// Repeats the pattern at least 'atLeast' times and at most 'atMost' times.
                    let rewritten = Pattern.repeat atLeast atMost r

                    // Process the rewritten expression.
                    return! validateAndSimplify rewritten
            }

        // Call the function which traverses the pattern to validate/preprocess it.
        validateAndSimplify pattern <| function
            | Choice2Of2 errors ->
                LazyList.toArray errors
                |> Choice2Of2
            | Choice1Of2 processedPattern ->
                Choice1Of2 processedPattern

    /// For special patterns such as 'eof' or the wildcard ("catch-all") pattern, get the earliest occurrence
    /// of a match-rule clause matching the pattern (if any). If multiple rule clauses match the pattern, emit
    /// warning messages for any clauses after the first one since they'll never be matched.
    let private tryGetEarliestMatchingClause (ruleClauses : RuleClause[]) (matchingClauseIndices : int<RuleClauseIdx>[]) =
        // Precondition: 'matchingClauseIndices' must be sorted.
        assert (matchingClauseIndices = Array.sort matchingClauseIndices)

        match matchingClauseIndices with
        | [| |] ->
            None
        | [| acceptingClauseIndex |] ->
            Some acceptingClauseIndex
        | _ ->
            // Only the earliest occurrence of the pattern will be matched.
            // TODO : Return warning messages (with location info) about patterns which will never be matched.
            // TEMP : In the meantime, print warnings to the debug console for development purposes.
            for i = 1 to matchingClauseIndices.Length - 1 do
                let clauseIndex = matchingClauseIndices.[i]
                let clausePosition = ruleClauses.[int clauseIndex].Pattern.PositionRange
                Debug.WriteLine (sprintf "This pattern will never be matched. (ClauseIndex = %i)" <| int clauseIndex)

            // Return the first (earliest) use of the matching pattern.
            Some matchingClauseIndices.[0]

    //
    // TODO :   Modify/rewrite this function so it uses the 'readerState' workflow.
    //          The read-only value will be the CompilationOptions record, and the state value will be the (macroEnv, badMacros).
    let private compileRule (rule : Rule) (options : CompilationOptions) (macroEnv, badMacros) =
        choice {
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
            List.revIntoArray rule.Clauses

        // Extract any clauses which match the end-of-file symbol;
        // these clauses need to be handled specially.
        let patterns, eofClauseIndices =
            ruleClauses
            |> Array.mapiPartition(fun idx clause ->
                // Extract the relevant information from the pattern of each clause,
                // based on which case of RuleClausePattern they're defined with.
                let ruleClauseIdx = tag<RuleClauseIdx> idx
                match clause.Pattern.Value with
                | Pattern pattern ->
                    Choice1Of2 (ruleClauseIdx, pattern)
                | EndOfFile ->
                    Choice2Of2 ruleClauseIdx)

        /// The index of the rule clause whose action will be executed
        /// if the lexer attempts to match this rule once the end-of-file
        /// has been reached.
        let eofAcceptingClauseIndex = tryGetEarliestMatchingClause ruleClauses eofClauseIndices

        /// The index of the wildcard rule clause, if this rule contains one.
        let wildcardAcceptingClauseIndex =
            patterns
            |> Array.choose (fun (idx, pat) ->
                match pat with
                | Any -> Some idx
                | _ -> None)
            |> tryGetEarliestMatchingClause ruleClauses

        // Validate and simplify the patterns of the rule clauses.
        let! ruleClauseRegexes =
            // Put all of the "results" in one array and all of the "errors" in another.
            let results, errors =
                patterns
                |> Array.mapPartition (fun (originalRuleClauseIndex, pattern) ->
                    validateAndSimplifyPattern pattern (macroEnv, badMacros, options)
                    |> Choice.map (fun pattern ->
                        originalRuleClauseIndex, pattern))

            // If there are any errors return them; otherwise, return the results.
            if Array.isEmpty errors then
                Choice1Of2 results
            else
                // Flatten the error array.
                Choice2Of2 <| Array.concat errors

        /// The DFA compiled from the rule clause patterns.
        let compiledPatternDfa =
            let regexOriginalClauseIndices, ruleClauseRegexes =
                Array.unzip ruleClauseRegexes

            rulePatternsToDfa ruleClauseRegexes regexOriginalClauseIndices

        // If this rule has a pattern accepting the end-of-file marker,
        // create an additional DFA state to serve as the EOF-accepting state
        // and create a transition edge labeled with the EOF symbol to it.
        let compiledPatternDfa =
            match eofAcceptingClauseIndex with
            | None ->
                compiledPatternDfa
            | Some eofAcceptingClauseIndex ->
                let eofAcceptingState, transitions =
                    compiledPatternDfa.Transitions.CreateVertex ()
                let transitions =
                    transitions.AddEofEdge compiledPatternDfa.InitialState eofAcceptingState
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
                    ||> TagMap.fold (fun ruleAlphabet _ targetMap ->
                        (ruleAlphabet, targetMap)
                        ||> TagMap.fold (fun ruleAlphabet _ edgeChars ->
                            CharSet.union ruleAlphabet edgeChars))

                /// The set of characters labelling the out-edges of the initial DFA state.
                let initialEdgeLabels =
                    let targetMap = TagMap.find 0<_> compiledPatternDfa.Transitions.AdjacencyMap
                    (CharSet.empty, targetMap)
                    ||> TagMap.fold (fun initialEdgeLabels _ edgeChars ->
                        CharSet.union initialEdgeLabels edgeChars)

                /// The characters matched by this rule's wildcard pattern.
                let wildcardChars =
                    // Augment the rule alphabet with the low ASCII characters,
                    // because that's how fslex does it and we need to be compatible (for now).
                    let ruleAlphabet =
                        CharSet.ofRange (char 0) (char 127)
                        |> CharSet.union ruleAlphabet

                    CharSet.difference ruleAlphabet initialEdgeLabels

                // If the set of characters matched by the wildcard pattern is not empty, create a new DFA state which
                // accepts the wildcard pattern, then add transition edges to it from the initial state.
                if CharSet.isEmpty wildcardChars then
                    // TODO : This warning shouldn't be emitted here -- it should be returned from this function so
                    //        if can be displayed to the user in whatever way makes sense for the consumer of this function.
                    //        Also, we want to return location information so it can be used to emit MSBuild-style warning
                    //        messages and/or text adornments in Visual Studio.
                    Debug.WriteLine "Warning: Wildcard pattern in rule will never be matched."

                    compiledPatternDfa
                else
                    let wildcardAcceptingState, transitions =
                        compiledPatternDfa.Transitions.CreateVertex ()
                    let transitions =
                        transitions.AddEdges compiledPatternDfa.InitialState wildcardAcceptingState wildcardChars

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
                List.revIntoArray rule.Parameters;
            RuleClauseActions =
                ruleClauses
                |> Array.map (fun clause ->
                    clause.Action); }
        }

    /// Creates pattern-matching DFAs from the lexer rules.
    let lexerSpec (spec : Specification) options =
        choice {
        // Validate and simplify the macros to create the macro table/environment.
        let! macroEnv =
            preprocessMacros spec.Macros options
            |> Choice.mapError (fun (macroEnv, badMacros, errors) ->
                // TODO : Validate the rule clauses, but don't compile the rule DFAs.
                // This way we can return all applicable errors instead of just those for the macros.
                errors)
            
        (* Compile the lexer rules *)
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

        // If there are any compilation errors, use them to set the
        // error value of the computation expression.
        if not <| Array.isEmpty compilationErrors then
            do! Choice.error <| Array.concat compilationErrors

        // Return a CompiledSpecification record created from the compiled rules.
        return {
            Header = spec.Header;
            Footer = spec.Footer;
            CompiledRules =
                (Map.empty, ruleIdentifiers, compiledRules)
                |||> Array.fold2 (fun map ({ Value = ruleId; PositionRange = _; }) compiledRule ->
                    Map.add ruleId compiledRule map); }
        }
