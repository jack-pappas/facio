(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpLex.Regex

open System.Diagnostics
open LanguagePrimitives
open SpecializedCollections

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
    static member private IsNullableImpl regex cont =
        match regex with
        | Epsilon
        | Star _ ->
            cont true
        | Any
        | CharacterSet _ ->
            cont false
        | Negate regex ->
            Regex.IsNullableImpl regex (cont >> not)
        | Concat (a, b)
        | And (a, b) ->
            // IsNullable(a) && IsNullable(b)
            Regex.IsNullableImpl a <| fun a ->
                if not a then false
                else
                    Regex.IsNullableImpl b cont
        | Or (a, b) ->
            // IsNullable(a) || IsNullable(b)
            Regex.IsNullableImpl a <| fun a ->
                if a then true
                else
                    Regex.IsNullableImpl b cont

    /// Determines if a specified Regex is 'nullable',
    /// i.e., it accepts the empty string (epsilon).
    static member IsNullable (regex : Regex) =
        Regex.IsNullableImpl regex id

    /// Implementation of the canonicalization function.
    static member private CanonicalizeImpl (regex : Regex) (cont : Regex -> Regex) =
        match regex with
        | Epsilon
        | Any as regex ->
            cont regex

        | CharacterSet charSet as charSetRegex ->
            match CharSet.count charSet with
            | 0 ->
                Regex.empty
            | 1 ->
                CharSet.minElement charSet
                |> Regex.ofChar
            | _ ->
                charSetRegex
            |> cont

        | Negate Empty ->
            cont Any
        | Negate Any ->
            cont Regex.empty
        | Negate Epsilon ->
            cont Regex.empty
        | Negate (Negate regex) ->
            Regex.CanonicalizeImpl regex cont
        | Negate r ->
            Regex.CanonicalizeImpl r <| fun r' ->
                Negate r'
                |> cont

        | Star (Star _ as ``r*``) ->
            Regex.CanonicalizeImpl ``r*`` cont
        | Star Epsilon
        | Star Empty ->
            cont Epsilon
        | Star (Or (Epsilon, r))
        | Star (Or (r, Epsilon)) ->
            Regex.CanonicalizeImpl r <| fun r' ->
                Star r'
                |> cont
        | Star r ->
            Regex.CanonicalizeImpl r <| fun r' ->
                Star r'
                |> cont

        | Concat (Empty, _)
        | Concat (_, Empty) ->
            cont Regex.empty
        | Concat (Epsilon, r)
        | Concat (r, Epsilon) ->
            Regex.CanonicalizeImpl r cont
        | Concat (r, Concat (s, t)) ->
            // Rewrite the expression so it's left-associative.
            let regex = Concat (Concat (r, s), t)
            Regex.CanonicalizeImpl regex cont        
        | Concat (r, s) ->
            Regex.CanonicalizeImpl r <| fun r' ->
            Regex.CanonicalizeImpl s <| fun s' ->
                // Try to simplify the expression, using the canonicalized components.
                match r', s' with
                | Empty, _
                | _, Empty ->
                    cont Regex.empty
                | Epsilon, r'
                | r', Epsilon ->
                    Regex.CanonicalizeImpl r' cont
                | r', s' ->
                    Concat (r', s')
                    |> cont

        | Or (Any, _)
        | Or (_, Any) ->
            cont Any
        | Or (Empty, r)
        | Or (r, Empty) ->
            Regex.CanonicalizeImpl r cont
        | Or (CharacterSet charSet1, CharacterSet charSet2) ->
            // 'Or' is the disjunction (union) of two Regexes.
            let charSetUnion = CharSet.union charSet1 charSet2

            // Return the simplest Regex for the union set.
            CharacterSet charSetUnion
            |> cont

        | Or (r, Or (s, t)) ->
            // Rewrite the expression so it's left-associative.
            let regex = Or (Or (r, s), t)
            Regex.CanonicalizeImpl regex cont
        | Or (r, s) ->
            Regex.CanonicalizeImpl r <| fun r' ->
            Regex.CanonicalizeImpl s <| fun s' ->
                // Try to simplify the expression, using the canonicalized components.
                match r', s' with
                | r', s' when r' = s' ->
                    cont r'

                | Empty, r
                | r, Empty ->
                    Regex.CanonicalizeImpl r cont

                | Any, _
                | _, Any ->
                    cont Any

                | CharacterSet charSet1, CharacterSet charSet2 ->
                    // 'Or' is the disjunction (union) of two Regexes.
                    let charSetUnion = CharSet.union charSet1 charSet2

                    // Return the simplest Regex for the union set.
                    CharacterSet charSetUnion
                    |> cont

                | r', s' ->
                    // Sort the components before returning; this takes care
                    // of the symmetry rule (r | s) = (s | r) so the
                    // "approximately equal" relation is simply handled by
                    // F#'s structural equality.
                    if r' < s'
                    then Or (r', s')
                    else Or (s', r')
                    |> cont
        
        | And (Any, r)
        | And (r, Any) ->
            Regex.CanonicalizeImpl r cont
        | And (Empty, _)
        | And (_, Empty) ->
            cont Regex.empty
        | And (CharacterSet charSet1, CharacterSet charSet2) ->
            // 'And' is the conjunction (intersection) of two Regexes.
            let charSetIntersection = CharSet.intersect charSet1 charSet2

            // Return the simplest Regex for the intersection set.
            CharacterSet charSetIntersection
            |> cont
        | And (r, And (s, t)) ->
            // Rewrite the expression so it's left-associative.
            let regex = And (And (r, s), t)
            Regex.CanonicalizeImpl regex cont
        | And (r, s) ->
            Regex.CanonicalizeImpl r <| fun r' ->
            Regex.CanonicalizeImpl s <| fun s' ->
                // Try to simplify the expression, using the canonicalized components.
                match r', s' with
                | r', s' when r' = s' ->
                    cont r'

                | Empty, _
                | _, Empty ->
                    cont Regex.empty

                | Any, r
                | r, Any ->
                    Regex.CanonicalizeImpl r cont

                | CharacterSet charSet1, CharacterSet charSet2 ->
                    // 'And' is the conjunction (intersection) of two Regexes.
                    let charSetIntersection = CharSet.intersect charSet1 charSet2

                    // Return the simplest Regex for the intersection set.
                    CharacterSet charSetIntersection
                    |> cont

                | r', s' ->
                    // Sort the components before returning; this takes care
                    // of the symmetry rule (r & s) = (s & r) so the
                    // "approximately equal" relation is simply handled by
                    // F#'s structural equality.
                    if r' < s'
                    then And (r', s')
                    else And (s', r')
                    |> cont

    /// Creates a new Regex in canonical form from the given Regex.
    static member Canonicalize (regex : Regex) : Regex =
        Regex.CanonicalizeImpl regex id

    //
    static member private DerivativeImpl wrtSymbol regex cont =
        match regex with
        | Epsilon ->
            cont Regex.empty
        | Star r as ``r*`` ->
            Regex.DerivativeImpl wrtSymbol r <| fun r' ->
                Concat (r', ``r*``)
                |> cont
        | Concat (r, s) ->
            let ``nu(r)`` = if Regex.IsNullable r then Epsilon else Regex.empty
            Regex.DerivativeImpl wrtSymbol r <| fun r' ->
            Regex.DerivativeImpl wrtSymbol s <| fun s' ->
                Or (Concat (r', s),
                    Concat (``nu(r)``, s'))
                |> cont
        | Or (r, s) ->
            Regex.DerivativeImpl wrtSymbol r <| fun r' ->
            Regex.DerivativeImpl wrtSymbol s <| fun s' ->
                Or (r', s')
                |> cont
        | And (r, s) ->
            Regex.DerivativeImpl wrtSymbol r <| fun r' ->
            Regex.DerivativeImpl wrtSymbol s <| fun s' ->
                And (r', s')
                |> cont

        | Any ->
            cont Epsilon
        | Negate r ->
            Regex.DerivativeImpl wrtSymbol r <| fun r' ->
                Negate r'
                |> cont
        | CharacterSet charSet ->
            if CharSet.contains wrtSymbol charSet
            then Epsilon
            else Regex.empty
            |> cont

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
    static member private DerivativeClassesImpl regex cont =
        match regex with
        | Epsilon ->
            DerivativeClasses.Universe
            |> cont
        | Any ->
            { DerivativeClasses.Universe
                with HasEmptySet = true; }
            |> cont
        | CharacterSet charSet ->
            { HasEmptySet = false;
              Elements = charSet;
              Negated = charSet; }
            |> cont
        | Negate r
        | Star r ->
            Regex.DerivativeClassesImpl r cont
        | Concat (r, s) ->
            if not <| Regex.IsNullable r then
                Regex.DerivativeClassesImpl r cont
            else
                Regex.DerivativeClassesImpl r <| fun ``C(r)`` ->
                Regex.DerivativeClassesImpl s <| fun ``C(s)`` ->
                    DerivativeClasses.Intersect (``C(r)``, ``C(s)``)
                    |> cont
        | Or (r, s)
        | And (r, s) ->
            Regex.DerivativeClassesImpl r <| fun ``C(r)`` ->
            Regex.DerivativeClassesImpl s <| fun ``C(s)`` ->
                DerivativeClasses.Intersect (``C(r)``, ``C(s)``)
                |> cont

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
        Array.map (Regex.Derivative symbol) regVec

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



