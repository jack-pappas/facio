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
open ExtCore.Control
open ExtCore.Control.Collections
open FSharpLex.SpecializedCollections

(*  Turn off warning about uppercase variable identifiers;
    some variables in the code below are named using the
    F# backtick syntax so they can use names which closely
    match those in the paper. *)
#nowarn "49"


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

    //
    [<CompiledName("Empty")>]
    static member empty =
        CharacterSet CharSet.empty

    //
    [<CompiledName("OfCharacter")>]
    static member ofChar c =
        CharacterSet <| CharSet.singleton c

    //
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

/// Active patterns for matching special cases of Regex.
[<AutoOpen>]
module private RegexPatterns =
    //
    let (|Empty|_|) regex =
        match regex with
        | CharacterSet charSet
            when CharSet.isEmpty charSet ->
            Some ()
        | _ ->
            None

    //
    let (|Character|_|) regex =
        match regex with
        | CharacterSet charSet
            when CharSet.count charSet = 1 ->
            Some <| CharSet.minElement charSet
        | _ ->
            None


// Add additional members to Regex.
type Regex with
    //
    static member private IsNullableImpl regex =
        Cps.cont {
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

    /// Implementation of the canonicalization function.
    static member private CanonicalizeImpl (regex : Regex) =
        Cps.cont {
        match regex with
        | Epsilon
        | Any as regex ->
            return regex
        | CharacterSet _ as charSetRegex ->
            return charSetRegex
        | Negate Empty ->
            return Any
        | Negate Any ->
            return Regex.empty
        | Negate Epsilon ->
            return Regex.empty
        | Negate (Negate regex) ->
            return! Regex.CanonicalizeImpl regex
        | Negate r ->
            let! r' = Regex.CanonicalizeImpl r
            return Negate r'

        | Star (Star _ as ``r*``) ->
            return! Regex.CanonicalizeImpl ``r*``
        | Star Epsilon
        | Star Empty ->
            return Epsilon
        | Star (Or (Epsilon, r))
        | Star (Or (r, Epsilon)) ->
            let! r' = Regex.CanonicalizeImpl r
            return Star r'
        | Star r ->
            let! r' = Regex.CanonicalizeImpl r
            return Star r'

        | Concat (Empty, _)
        | Concat (_, Empty) ->
            return Regex.empty
        | Concat (Epsilon, r)
        | Concat (r, Epsilon) ->
            return! Regex.CanonicalizeImpl r
        | Concat (r, Concat (s, t)) ->
            // Rewrite the expression so it's left-associative.
            let regex = Concat (Concat (r, s), t)
            return! Regex.CanonicalizeImpl regex
        | Concat (r, s) ->
            let! r' = Regex.CanonicalizeImpl r
            let! s' = Regex.CanonicalizeImpl s

            // Try to simplify the expression, using the canonicalized components.
            match r', s' with
            | Empty, _
            | _, Empty ->
                return Regex.empty
            | Epsilon, r'
            | r', Epsilon ->
                return! Regex.CanonicalizeImpl r'
            | r', s' ->
                return Concat (r', s')

        | Or (Any, _)
        | Or (_, Any) ->
            return Any
        | Or (Empty, r)
        | Or (r, Empty) ->
            return! Regex.CanonicalizeImpl r
        | Or (CharacterSet charSet1, CharacterSet charSet2) ->
            // 'Or' is the disjunction (union) of two Regexes.
            let charSetUnion = CharSet.union charSet1 charSet2

            // Return the simplest Regex for the union set.
            return CharacterSet charSetUnion

        | Or (r, Or (s, t)) ->
            // Rewrite the expression so it's left-associative.
            let regex = Or (Or (r, s), t)
            return! Regex.CanonicalizeImpl regex
        | Or (r, s) ->
            let! r' = Regex.CanonicalizeImpl r
            let! s' = Regex.CanonicalizeImpl s

            // Try to simplify the expression, using the canonicalized components.
            match r', s' with
            | r', s' when r' = s' ->
                return r'

            | Empty, r
            | r, Empty ->
                return! Regex.CanonicalizeImpl r

            | Any, _
            | _, Any ->
                return Any

            | CharacterSet charSet1, CharacterSet charSet2 ->
                // 'Or' is the disjunction (union) of two Regexes.
                let charSetUnion = CharSet.union charSet1 charSet2

                // Return the simplest Regex for the union set.
                return CharacterSet charSetUnion

            | r', s' ->
                // Sort the components before returning; this takes care
                // of the symmetry rule (r | s) = (s | r) so the
                // "approximately equal" relation is simply handled by
                // F#'s structural equality.
                return
                    if r' < s'
                    then Or (r', s')
                    else Or (s', r')
        
        | And (Any, r)
        | And (r, Any) ->
            return! Regex.CanonicalizeImpl r
        | And (Empty, _)
        | And (_, Empty) ->
            return Regex.empty
        | And (CharacterSet charSet1, CharacterSet charSet2) ->
            // 'And' is the conjunction (intersection) of two Regexes.
            let charSetIntersection = CharSet.intersect charSet1 charSet2

            // Return the simplest Regex for the intersection set.
            return CharacterSet charSetIntersection
        | And (r, And (s, t)) ->
            // Rewrite the expression so it's left-associative.
            let regex = And (And (r, s), t)
            return! Regex.CanonicalizeImpl regex
        | And (r, s) ->
            let! r' = Regex.CanonicalizeImpl r
            let! s' = Regex.CanonicalizeImpl s

            // Try to simplify the expression, using the canonicalized components.
            match r', s' with
            | r', s' when r' = s' ->
                return r'

            | Empty, _
            | _, Empty ->
                return Regex.empty

            | Any, r
            | r, Any ->
                return! Regex.CanonicalizeImpl r

            | CharacterSet charSet1, CharacterSet charSet2 ->
                // 'And' is the conjunction (intersection) of two Regexes.
                let charSetIntersection = CharSet.intersect charSet1 charSet2

                // Return the simplest Regex for the intersection set.
                return CharacterSet charSetIntersection

            | r', s' ->
                // Sort the components before returning; this takes care
                // of the symmetry rule (r & s) = (s & r) so the
                // "approximately equal" relation is simply handled by
                // F#'s structural equality.
                return
                    if r' < s'
                    then And (r', s')
                    else And (s', r')
        }

    /// Creates a new Regex in canonical form from the given Regex.
    static member Canonicalize (regex : Regex) : Regex =
        Regex.CanonicalizeImpl regex id

    //
    static member private DerivativeImpl wrtSymbol regex =
        Cps.cont {
        match regex with
        | Epsilon ->
            return Regex.empty
        | Star r as ``r*`` ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            return Concat (r', ``r*``)

        | Concat (r, s) ->
            let ``nu(r)`` = if Regex.IsNullable r then Epsilon else Regex.empty
            let! r' = Regex.DerivativeImpl wrtSymbol r
            let! s' = Regex.DerivativeImpl wrtSymbol s
            return
                Or (Concat (r', s),
                    Concat (``nu(r)``, s'))
        | Or (r, s) ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            let! s' = Regex.DerivativeImpl wrtSymbol s
            return Or (r', s')
        | And (r, s) ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            let! s' = Regex.DerivativeImpl wrtSymbol s
            return And (r', s')

        | Any ->
            return Epsilon
        | Negate r ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            return Negate r'
        | CharacterSet charSet ->
            return
                if CharSet.contains wrtSymbol charSet
                then Epsilon
                else Regex.empty
        }

    /// Computes the derivative of a Regex with respect to a specified symbol.
    static member Derivative symbol regex =
        Regex.DerivativeImpl symbol regex id


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

// Add more members to Regex
type Regex with
    //
    static member private DerivativeClassesImpl regex =
        Cps.cont {
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

/// An array of regular expressions.
// Definition 4.3.
type RegularVector = Regex[]

/// Functional programming operators related to the RegularVector type.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module RegularVector =
    open LanguagePrimitives

    /// Compute the derivative of a regular vector
    /// with respect to the given symbol.
    let inline derivative symbol (regVec : RegularVector) : RegularVector =
        #if PARALLEL_FX
        Array.Parallel.map (Regex.Derivative symbol) regVec
        #else
        Array.map (Regex.Derivative symbol) regVec
        #endif

    /// Determines if the regular vector is nullable,
    /// i.e., it accepts the empty string (epsilon).
    let inline isNullable (regVec : RegularVector) =
        // A regular vector is nullable iff any of
        // the component regexes are nullable.
        Array.exists Regex.IsNullable regVec

    /// The indices of the element expressions (if any)
    /// that accept the empty string (epsilon).
    let acceptingElements (regVec : RegularVector) =
        /// The indices of the expressions accepting the empty string.
        let mutable accepting = Set.empty

        let len = Array.length regVec
        for i = 0 to len - 1 do
            if Regex.IsNullable regVec.[i] then
                accepting <- Set.add i accepting

        // Return the computed set of indices.
        accepting

    /// Determines if a regular vector is an empty vector. Note that an
    /// empty regular vector is *not* the same thing as an empty array.
    let inline isEmpty (regVec : RegularVector) =
        // A regular vector is empty iff all of it's entries
        // are equal to the empty character set.
        regVec
        |> Array.forall (function
            | CharacterSet charSet ->
                CharSet.isEmpty charSet
            | _ -> false)

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

    /// Creates a new regular vector in canonical form by canonicalizing
    /// each regular expression in the given regular vector.
    let inline canonicalize (regVec : RegularVector) : RegularVector =
        Array.map Regex.Canonicalize regVec



