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
module FSharpLex.Regex

open System.Diagnostics
open LanguagePrimitives
open ExtCore
open ExtCore.Collections
open ExtCore.Control.Cps
open ExtCore.Control.Collections
open FSharpLex.SpecializedCollections

(*  Turn off warning about uppercase variable identifiers;
    some variables in the code below are named using the
    F# backtick syntax so they can use names which closely
    match those in the paper. *)
#nowarn "49"

//
type DerivativeClasses = {
    /// When set, indicates that this set of
    /// derivative classes includes the empty set.
    HasEmptySet : bool;
    //
    Elements : CharSet;
    //
    Negated : CharSet;
} with
    //
    static member Universe =
        {   HasEmptySet = false;
            Elements = CharSet.empty;
            Negated = CharSet.empty; }

    /// Computes a conservative approximation of the intersection of two sets of
    /// derivative classes. This is needed when computing the set of derivative
    /// classes for a compound regular expression ('And', 'Or', and 'Concat').
    static member Intersect (``C(r)``, ``C(s)``) =
        {   HasEmptySet =
                ``C(r)``.HasEmptySet || ``C(s)``.HasEmptySet;
            Elements =
                CharSet.union ``C(r)``.Elements ``C(s)``.Elements;
            Negated =
                CharSet.union ``C(r)``.Negated ``C(s)``.Negated; }


/// <summary>A regular expression.</summary>
/// <remarks>This type includes some cases which are normally referred to as "extended"
/// regular expressions. However, only those cases which are still closed under boolean
/// operations are included here, so the lanugage it represents must still be a regular
/// language.</remarks>
[<DebuggerDisplay("{DebuggerDisplay,nq}")>]
type Regex =
    /// The empty string.
    | Epsilon
    /// Kleene *-closure.
    /// The specified Regex will be matched zero (0) or more times.
    | Star of Regex
    /// Concatenation. A Regex immediately followed by another Regex.
    | Concat of Regex * Regex
    /// Choice between two regular expressions (i.e., boolean OR).
    | Or of Regex * Regex
    /// Boolean AND of two regular expressions.
    | And of Regex * Regex

    /// Negation.
    | Negate of Regex
    /// A set of characters.
    | CharacterSet of CharSet

    (* TODO :   Remove this -- Pattern.Any should compile
                into standard regexes for simplicity. *)
    /// Any character.
    | Any

    /// Infrastructure. Only for use with DebuggerDisplayAttribute.
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private this.DebuggerDisplay
        with get () =
            match this with
            | Epsilon ->
                "\u03f5"    // Epsilon symbol
            | CharacterSet charSet
                when CharSet.isEmpty charSet ->
                "Empty"
            | CharacterSet charSet
                when CharSet.count charSet = 1 ->
                let c = CharSet.minElement charSet
                c.ToString ()
            | regex ->
                // TODO : Finish this for the other regex cases.
                // It would be nice if this would print the regex in usual printed form.
                sprintf "%A" regex

    /// Determines if a specified Regex is 'nullable',
    /// i.e., it accepts the empty string (epsilon).
    static member private IsNullableImpl regex =
        cont {
        match regex with
        | Epsilon
        | Star _ ->
            return true
        | Any
        | CharacterSet _ ->
            return false
        | Negate regex ->
            let! result = Regex.IsNullableImpl regex
            return not result
        | Concat (a, b)
        | And (a, b) ->
            // IsNullable(a) && IsNullable(b)
            let! aNullable = Regex.IsNullableImpl a
            if aNullable then
                return! Regex.IsNullableImpl b
            else
                return false
        | Or (a, b) ->
            // IsNullable(a) || IsNullable(b)
            let! aNullable = Regex.IsNullableImpl a
            if aNullable then
                return true
            else
                return! Regex.IsNullableImpl b
        }

    /// Determines if a specified Regex is 'nullable',
    /// i.e., it accepts the empty string (epsilon).
    static member IsNullable (regex : Regex) =
        Regex.IsNullableImpl regex id


/// 'Smart' constructors for Regex.
/// These should *always* be used to create new Regex instances because they ensure the
/// resulting Regex is in a normal form; this is very important for minimizing the number
/// of states in the DFA constructed from the Regex.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Regex =
    /// The regular expression which never matches (accepts) anything.
    [<CompiledName("Empty")>]
    let empty : Regex =
        CharacterSet CharSet.empty

    /// Is the regular expression empty?
    [<CompiledName("IsEmpty")>]
    let isEmpty regex =
        match regex with
        | CharacterSet charSet ->
            CharSet.isEmpty charSet
        | _ ->
            false

    /// The 'epsilon' pattern, which matches (accepts) an empty string.
    [<CompiledName("Epsilon")>]
    let epsilon : Regex =
        Epsilon

    /// Returns a new regular expression which matches exactly one (1) instance of the specified character.
    [<CompiledName("OfCharacter")>]
    let inline ofChar c =
        CharacterSet <| CharSet.singleton c

    /// Returns a new regular expression which matches exactly one (1) instance
    /// of any character in the specified set.
    [<CompiledName("OfCharSet")>]
    let inline ofCharSet (set : CharSet) : Regex =
        CharacterSet set

    /// Creates a normalized Regex.Negate from the specified Regex.
    [<CompiledName("CreateNegate")>]
    let rec negate (regex : Regex) : Regex =
        match regex with
        | Negate (Negate regex) ->
            negate regex
        | Negate regex ->
            regex
        | _ ->
            Negate regex

    /// Returns a new regular expression which matches the given
    /// regular expression zero or more times.
    [<CompiledName("CreateStar")>]
    let rec star (regex : Regex) : Regex =
        match regex with
        | Epsilon ->
            Epsilon
        | CharacterSet charSet
            when CharSet.isEmpty charSet ->
            Epsilon
        | Or (Epsilon, regex)
        | Or (regex, Epsilon)
        | Star regex ->
            star regex
        | _ ->
            Star regex

    //
    let rec private concatImpl (regex1 : Regex) (regex2 : Regex) =
        cont {
        match regex1, regex2 with
        | regex, Epsilon
        | Epsilon, regex ->
            return regex
        | CharacterSet charSet, _
        | _, CharacterSet charSet
            when CharSet.isEmpty charSet ->
            return empty

        // Nested Concat patterns should skew towards the right.
        | Concat (r, s), t ->
            let! s' = concatImpl s t
            return! concatImpl r s'

        | _, _ ->
            return Concat (regex1, regex2)
        }

    /// Concatenates two regular expressions so they'll be matched sequentially.
    [<CompiledName("CreateConcat")>]
    let concat (regex1 : Regex) (regex2 : Regex) : Regex =
        // Call the recursive implementation.
        concatImpl regex1 regex2 id

    //
    let rec private andImpl (regex1 : Regex) (regex2 : Regex) =
        cont {
        match regex1, regex2 with
        | CharacterSet charSet, _
        | _, CharacterSet charSet
            when CharSet.isEmpty charSet ->
            return empty

        | Any, regex
        | regex, Any ->
            return regex

        // Nested And patterns should skew towards the right.
        | And (r, s), t ->
            let! s' = andImpl s t
            return! andImpl r s'

        | _, _ ->
            if regex1 = regex2 then
                return regex1
            else
                // Compare/sort the two regexes. This simplifies the compilation code and
                // also -- crucially -- speeds it up since it allows the compiler-generated structural
                // equality code to be used as an (approximate) equivalence test.
                if regex2 < regex1 then
                    return And (regex2, regex1)
                else
                    return And (regex1, regex2)
        }

    /// Conjunction of two regular expressions.
    /// This returns a new regular expression which matches an input string
    /// if and only if the input matches both of the given regular expressions.
    [<CompiledName("CreateAnd")>]
    let andr (regex1 : Regex) (regex2 : Regex) : Regex =
        // Call the recursive implementation.
        andImpl regex1 regex2 id

    //
    let rec private orImpl (regex1 : Regex) (regex2 : Regex) =
        cont {
        match regex1, regex2 with
        | CharacterSet charSet, regex
        | regex, CharacterSet charSet
            when CharSet.isEmpty charSet ->
            return regex

        | Any, _
        | _, Any ->
            return Any

        // Nested Or patterns should skew towards the right.
        | Or (r, s), t ->
            let! s' = orImpl s t
            return! orImpl r s'

        | _, _ ->
            if regex1 = regex2 then
                return regex1
            else
                // Compare/sort the two regexes. This simplifies the compilation code and
                // also -- crucially -- speeds it up since it allows the compiler-generated structural
                // equality code to be used as an (approximate) equivalence test.
                if regex2 < regex1 then
                    return Or (regex2, regex1)
                else
                    return Or (regex1, regex2)
        }

    /// Disjunction of two regular expressions.
    /// This returns a new regular expression which matches an input string
    /// when the input matches either (or both) of the given regular expressions.
    [<CompiledName("CreateOr")>]
    let orr (regex1 : Regex) (regex2 : Regex) : Regex =
        // Call the recursive implementation.
        orImpl regex1 regex2 id


// Add derivative methods to Regex.
type Regex with
    /// Computes the derivative of a Regex with respect to a specified symbol.
    static member private DerivativeImpl wrtSymbol regex =
        cont {
        match regex with
        | Epsilon ->
            return Regex.empty
        | Star r as ``r*`` ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            return Regex.concat r' ``r*``

        | Concat (r, s) ->
            let ``nu(r)`` = if Regex.IsNullable r then Regex.epsilon else Regex.empty
            let! r' = Regex.DerivativeImpl wrtSymbol r
            let! s' = Regex.DerivativeImpl wrtSymbol s

            let or_r = Regex.concat r' s
            let or_s = Regex.concat ``nu(r)`` s'
            return Regex.orr or_r or_s

        | Or (r, s) ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            let! s' = Regex.DerivativeImpl wrtSymbol s
            return Regex.orr r' s'

        | And (r, s) ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            let! s' = Regex.DerivativeImpl wrtSymbol s
            return Regex.andr r' s'

        | Any ->
            return Regex.epsilon

        | Negate r ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            return Regex.negate r'

        | CharacterSet charSet ->
            return
                if CharSet.contains wrtSymbol charSet then
                    Regex.epsilon
                else
                    Regex.empty
        }

    /// Computes the derivative of a Regex with respect to a specified symbol.
    static member Derivative symbol regex =
        Regex.DerivativeImpl symbol regex id

    /// Computes an approximate set of derivative classes for the specified Regex.
    static member private DerivativeClassesImpl regex =
        cont {
        match regex with
        | Epsilon ->
            return DerivativeClasses.Universe
        | Any ->
            return
                { DerivativeClasses.Universe
                    with HasEmptySet = true; }
        | CharacterSet charSet ->
            return
                { HasEmptySet = false;
                  Elements = charSet;
                  Negated = charSet; }
        | Negate r
        | Star r ->
            return! Regex.DerivativeClassesImpl r
        | Concat (r, s) ->
            if not <| Regex.IsNullable r then
                return! Regex.DerivativeClassesImpl r
            else
                let! ``C(r)`` = Regex.DerivativeClassesImpl r
                let! ``C(s)`` = Regex.DerivativeClassesImpl s
                return DerivativeClasses.Intersect (``C(r)``, ``C(s)``)
        | Or (r, s)
        | And (r, s) ->
            let! ``C(r)`` = Regex.DerivativeClassesImpl r
            let! ``C(s)`` = Regex.DerivativeClassesImpl s
            return DerivativeClasses.Intersect (``C(r)``, ``C(s)``)
        }

    /// Computes an approximate set of derivative classes for the specified Regex.
    static member DerivativeClasses (regex : Regex) =
        Regex.DerivativeClassesImpl regex id


////
//type RegexApproximateEqualityComparer () =
//    //
//    static member private ApproxEqualImpl (regex1, regex2) =
//        cont {
//        match regex1, regex2 with
//        //
//        
//
//
//
//        | _, _ ->
//            return notImpl "RegexSimilarityComparer.SimilarImpl"
//        }
//
//    //
//    static member ApproxEqual (regex1, regex2) : bool =
//        RegexApproximateEqualityComparer.ApproxEqualImpl (regex1, regex2) id


/// An array of regular expressions.
// Definition 4.3.
type RegularVector = Regex[]

/// Functional programming operators related to the RegularVector type.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module RegularVector =
    open LanguagePrimitives

    /// Compute the derivative of a regular vector
    /// with respect to the given symbol.
    let (*inline*) derivative symbol (regVec : RegularVector) : RegularVector =
        Array.map (Regex.Derivative symbol) regVec

    /// Determines if the regular vector is nullable,
    /// i.e., it accepts the empty string (epsilon).
    let (*inline*) isNullable (regVec : RegularVector) =
        // A regular vector is nullable iff any of
        // the component regexes are nullable.
        Array.exists Regex.IsNullable regVec

    /// The indices of the element expressions (if any)
    /// that accept the empty string (epsilon).
    let acceptingElements (regVec : RegularVector) =
        // Find the indices of the expressions accepting the empty string.
        (Set.empty, regVec)
        ||> Array.foldi (fun accepting i regex ->
            if Regex.IsNullable regex then
                Set.add i accepting
            else
                accepting)

    /// Determines if a regular vector is an empty vector. Note that an
    /// empty regular vector is *not* the same thing as an empty array.
    let (*inline*) isEmpty (regVec : RegularVector) =
        // A regular vector is empty iff all of it's entries
        // are equal to the empty character set.
        Array.forall Regex.isEmpty regVec

    /// Compute the approximate set of derivative classes of a regular vector.
    let derivativeClasses (regVec : RegularVector) =
        // Preconditions
        if Array.isEmpty regVec then
            invalidArg "regVec" "The regular vector does not contain any regular expressions."

        regVec
        // Compute the approximate set of derivative classes
        // for each regular expression in the vector.
        |> Array.map Regex.DerivativeClasses
        // By Definition 4.3, the approximate set of derivative classes
        // of a regular vector is the intersection of the approximate
        // sets of derivative classes of it's elements.
        |> Array.reduce (
            FuncConvert.FuncFromTupled DerivativeClasses.Intersect)

