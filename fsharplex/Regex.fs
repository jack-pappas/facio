(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpLex.Regex

open LanguagePrimitives
open SpecializedCollections


/// <summary>A regular expression.</summary>
/// <remarks>This type includes some cases which are normally referred to as "extended"
/// regular expressions. However, only those cases which are still closed under boolean
/// operations are included here, so the lanugage it represents must still be a regular
/// language.</remarks>
type Regex =
    /// The empty string.
    | Epsilon
    /// The empty language.
    | Empty    
    /// Any character except for newline ('\n').
    | Any
    /// A character.
    | Character of char
    /// A set of characters.
    // NOTE : Whenever a Regex is in "canonical" form, this set
    // will never contain fewer than two (2) characters.
    | CharacterSet of CharSet
    /// Negation.
    | Negate of Regex
    /// Kleene *-closure.
    /// The specified Regex will be matched zero (0) or more times.
    | Star of Regex
    /// Concatenation. A Regex immediately followed by another Regex.
    | Concat of Regex * Regex
    /// Choice between two regular expressions (i.e., boolean OR).
    | Or of Regex * Regex
    /// Boolean AND of two regular expressions.
    | And of Regex * Regex

    //
    static member private IsNullableImpl regex cont =
        match regex with
        | Epsilon
        | Star _ ->
            cont true
        | Empty
        | Any
        | Character _
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

    //
    static member private DerivativeImpl wrtSymbol regex cont =
        match regex with
        | Empty
        | Epsilon ->
            cont Empty
        | Any ->
            raise <| System.NotImplementedException "DerivativeImpl"
        | Character c ->
            if c = wrtSymbol then Epsilon else Empty
            |> cont
        | CharacterSet charSet ->
            if CharSet.contains wrtSymbol charSet then Epsilon else Empty
            |> cont
        | Negate r ->
            Regex.DerivativeImpl wrtSymbol r <| fun r' ->
                Negate r'
                |> cont
        | Star r as ``r*`` ->
            Regex.DerivativeImpl wrtSymbol r <| fun r' ->
                Concat (r', ``r*``)
                |> cont
        | Concat (r, s) ->
            Regex.DerivativeImpl wrtSymbol r <| fun r' ->
            Regex.DerivativeImpl wrtSymbol s <| fun s' ->
                let ``nu(r)`` = if Regex.IsNullable r then Epsilon else Empty
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

    /// Computes the derivative of a Regex with respect to a specified symbol.
    static member Derivative symbol regex =
        Regex.DerivativeImpl symbol regex id

    /// Given a CharSet from a CharacterSet case, returns the simplest Regex
    /// representing the CharSet.
    static member inline private SimplifyCharacterSet (charSet : CharSet) =
        match CharSet.count charSet with
        | 0 ->
            Empty
        | 1 ->
            CharSet.minElement charSet
            |> Character
        | _ ->
            CharacterSet charSet

    //
    static member private CanonicalizeImpl (regex : Regex) (charUniverse : CharSet) (cont : Regex -> Regex) =
        match regex with
        | Empty
        | Epsilon
        | Any
        | Character _ as regex ->
            cont regex

        | CharacterSet charSet as charSetRegex ->
            match CharSet.count charSet with
            | 0 ->
                Empty
            | 1 ->
                CharSet.minElement charSet
                |> Character
            | _ ->
                charSetRegex
            |> cont

        | Negate Empty ->
            cont Any
        | Negate Any ->
            cont Empty        
        | Negate (Character c) ->
             let anyMinusChar = CharSet.remove c charUniverse
             Regex.SimplifyCharacterSet anyMinusChar
             |> cont
        | Negate (CharacterSet charSet) ->
             let anyMinusCharSet = CharSet.difference charUniverse charSet
             Regex.SimplifyCharacterSet anyMinusCharSet
             |> cont
        | Negate (Negate regex) ->
            Regex.CanonicalizeImpl regex charUniverse cont
        | Negate _ as notRegex ->
            // This regex is canonical
            cont notRegex

        | Star (Star _ as ``r*``) ->
            Regex.CanonicalizeImpl ``r*`` charUniverse cont
        | Star Epsilon
        | Star Empty ->
            cont Epsilon
        | Star (Or (Epsilon, r))
        | Star (Or (r, Epsilon)) ->
            Regex.CanonicalizeImpl r charUniverse <| fun r' ->
                Star r'
                |> cont
        | Star _ as ``r*`` ->
            // This regex is canonical
            cont ``r*``

        | Concat (r, Concat (s, t)) ->
            // Rewrite the expression so it's left-associative.
            let regex = Concat (Concat (r, s), t)
            Regex.CanonicalizeImpl regex charUniverse cont        
        | Concat (r, s) ->
            Regex.CanonicalizeImpl r charUniverse <| fun r' ->
            Regex.CanonicalizeImpl s charUniverse <| fun s' ->
                // Try to simplify the expression, using the canonicalized components.
                match r', s' with
                | Empty, _
                | _, Empty ->
                    cont Empty
                | Epsilon, regex
                | regex, Epsilon ->
                    Regex.CanonicalizeImpl regex charUniverse cont
                | r', s' ->
                    Concat (r', s')
                    |> cont

        | Or (Empty, r)
        | Or (r, Empty) ->
            Regex.CanonicalizeImpl r charUniverse cont
        | Or (Any, _)
        | Or (_, Any) ->
            cont Any
        | Or (r, Or (s, t)) ->
            // Rewrite the expression so it's left-associative.
            let regex = Or (Or (r, s), t)
            Regex.CanonicalizeImpl regex charUniverse cont
        | Or (r, s) ->
            Regex.CanonicalizeImpl r charUniverse <| fun r' ->
            Regex.CanonicalizeImpl s charUniverse <| fun s' ->
                // Try to simplify the expression, using the canonicalized components.
                match r', s' with
                | r', s' when r' = s' ->
                    r'
                | (Character c1 as charRegex), Character c2 ->
                    if c1 = c2 then charRegex
                    else
                        CharSet.empty
                        |> CharSet.add c1
                        |> CharSet.add c2
                        |> CharacterSet

                | Character c, CharacterSet charSet
                | CharacterSet charSet, Character c ->
                    CharSet.add c charSet
                    |> CharacterSet

                | CharacterSet charSet1, CharacterSet charSet2 ->
                    // 'Or' is the disjunction (union) of two Regexes.
                    let charSetUnion = CharSet.union charSet1 charSet2

                    // Return the simplest Regex for the union set.
                    Regex.SimplifyCharacterSet charSetUnion

                | r', s' ->
                    // Sort the components before returning; this takes care
                    // of the symmetry rule (r | s) = (s | r) so the
                    // "approximately equal" relation is simply handled by
                    // F#'s structural equality.
                    if r' < s' then Or (r', s')
                    else Or (s', r')
                |> cont
        
        | And (Empty, _)
        | And (_, Empty) ->
            cont Empty
        | And (Any, r)
        | And (r, Any) ->
            Regex.CanonicalizeImpl r charUniverse cont
        | And (r, And (s, t)) ->
            // Rewrite the expression so it's left-associative.
            let regex = And (And (r, s), t)
            Regex.CanonicalizeImpl regex charUniverse cont
        | And (r, s) ->
            Regex.CanonicalizeImpl r charUniverse <| fun r' ->
            Regex.CanonicalizeImpl s charUniverse <| fun s' ->
                // Try to simplify the expression, using the canonicalized components.
                match r', s' with
                | r', s' when r' = s' ->
                    r'
                | (Character c1 as charRegex), Character c2 ->
                    if c1 = c2 then charRegex
                    else
                        // TODO : Emit a warning to TraceListener?
                        // The 'And' case represents a conjunction (intersection) of two Regexes;
                        // since the characters are different, the intersection must be empty.
                        Empty

                | Character c, CharacterSet charSet
                | CharacterSet charSet, Character c ->
                    CharSet.add c charSet
                    |> CharacterSet

                | CharacterSet charSet1, CharacterSet charSet2 ->
                    // 'And' is the conjunction (intersection) of two Regexes.
                    let charSetIntersection = CharSet.intersect charSet1 charSet2

                    // Return the simplest Regex for the intersection set.
                    Regex.SimplifyCharacterSet charSetIntersection

                | r', s' ->
                    // Sort the components before returning; this takes care
                    // of the symmetry rule (r & s) = (s & r) so the
                    // "approximately equal" relation is simply handled by
                    // F#'s structural equality.
                    if r' < s' then And (r', s')
                    else And (s', r')
                |> cont

    /// Creates a new Regex in canonical form from the given Regex.
    static member Canonicalize (regex : Regex, charUniverse) : Regex =
        // Preconditions
        if CharSet.isEmpty charUniverse then
            invalidArg "charUniverse" "The character universe (set of all characters used in the lexer) is empty."
        
        Regex.CanonicalizeImpl regex charUniverse id

    /// Computes a conservative approximation of the derivative class of
    /// a compound regular expression ('And', 'Or', and 'Concat') from
    /// the derivative classes of its component expressions.
    static member private DerivativeClassOfCompoundRegex (``C(r)``, ``C(s)``) =
        (Set.empty, ``C(r)``)
        ||> Set.fold (fun intersections el1 ->
            (intersections, ``C(s)``)
            ||> Set.fold (fun intersections el2 ->
                // The intersection of the two elements (character sets)
                let elementIntersection = CharSet.intersect el1 el2

                // Add the intersection to the set of intersections
                // (if it's already in the set, no error is thrown).
                Set.add elementIntersection intersections))

    //
    static member private DerivativeClassesImpl regex universe cont =
        match regex with
        | Epsilon
        | Empty ->
            Set.singleton universe
            |> cont
        | Any ->
            Set.singleton universe
            |> Set.add CharSet.empty
            |> cont
        | Character c ->
            Set.singleton (CharSet.singleton c)
            |> Set.add (CharSet.remove c universe)
            |> cont
        | CharacterSet charSet ->
            Set.singleton charSet
            |> Set.add (CharSet.difference universe charSet)
            |> cont
        | Negate r
        | Star r ->
            Regex.DerivativeClassesImpl r universe cont
        | Concat (r, s) ->
            if not <| Regex.IsNullable r then
                Regex.DerivativeClassesImpl r universe cont
            else
                Regex.DerivativeClassesImpl r universe <| fun ``C(r)`` ->
                Regex.DerivativeClassesImpl s universe <| fun ``C(s)`` ->
                    Regex.DerivativeClassOfCompoundRegex (``C(r)``, ``C(s)``)
                    |> cont
        | Or (r, s)
        | And (r, s) ->
            Regex.DerivativeClassesImpl r universe <| fun ``C(r)`` ->
            Regex.DerivativeClassesImpl s universe <| fun ``C(s)`` ->
                Regex.DerivativeClassOfCompoundRegex (``C(r)``, ``C(s)``)
                |> cont

    /// Computes the _approximate_ set of derivative classes for the specified Regex.
    static member DerivativeClasses (regex : Regex, charUniverse) =
        // Preconditions
        if CharSet.isEmpty charUniverse then
            invalidArg "charUniverse" "The character universe (set of all characters used in the lexer) is empty."
        
        Regex.DerivativeClassesImpl regex charUniverse id


/// An extended regular expression: a standard regular expression
/// plus some additional common cases for convenience.
type ExtendedRegex =
    (* Regex cases *)
    /// The empty string.
    | Epsilon
    /// A set of characters.
    | CharacterSet of CharSet
    /// Negation.
    | Negate of ExtendedRegex
    /// Kleene *-closure.
    /// The specified ExtendedRegex will be matched zero (0) or more times.
    | Star of ExtendedRegex
    /// Concatenation. A ExtendedRegex immediately followed by another ExtendedRegex.
    | Concat of ExtendedRegex * ExtendedRegex
    /// Choice between two regular expressions (i.e., boolean OR).
    | Or of ExtendedRegex * ExtendedRegex
    /// Boolean AND of two regular expressions.
    | And of ExtendedRegex * ExtendedRegex

    (* Extensions *)
    /// The empty language.
    | Empty
    /// Any character except for newline ('\n').
    | Any
    /// A character.
    | Character of char

    /// The specified ExtendedRegex is matched one (1) or more times.
    /// This is the Plus (+) operator in a regular expression.
    | OneOrMore of ExtendedRegex
    /// The specified ExtendedRegex is optionally matched (i.e., it will
    /// be matched zero (0) or one (1) times).
    /// This is the QuestionMark (?) operator in a regular expression.
    | Optional of ExtendedRegex
    /// Match the specified ExtendedRegex at least
    /// 'm' times and at most 'n' times.
    /// This is the {} operator in a regular expression.
    | Repetition of ExtendedRegex * uint32 option * uint32 option

    //
    static member private ToRegexImpl (extRegex : ExtendedRegex) cont : Regex =
        match extRegex with
        | ExtendedRegex.Empty ->
            cont Regex.Empty
        | ExtendedRegex.Epsilon ->
            cont Regex.Epsilon
        | ExtendedRegex.Any ->
            cont Regex.Any
        | ExtendedRegex.Character c ->
            Regex.Character c
            |> cont
        | ExtendedRegex.CharacterSet charSet ->
            Regex.CharacterSet charSet
            |> cont

        | ExtendedRegex.Negate r ->
            ExtendedRegex.ToRegexImpl r <| fun r ->
                Regex.Negate r
                |> cont

        | ExtendedRegex.Star r ->
            ExtendedRegex.ToRegexImpl r <| fun r ->
                Regex.Star r
                |> cont

        | ExtendedRegex.Concat (r, s) ->
            ExtendedRegex.ToRegexImpl r <| fun r ->
            ExtendedRegex.ToRegexImpl s <| fun s ->
                Regex.Concat (r, s)
                |> cont

        | ExtendedRegex.Or (r, s) ->
            ExtendedRegex.ToRegexImpl r <| fun r ->
            ExtendedRegex.ToRegexImpl s <| fun s ->
                Regex.Or (r, s)
                |> cont

        | ExtendedRegex.And (r, s) ->
            ExtendedRegex.ToRegexImpl r <| fun r ->
            ExtendedRegex.ToRegexImpl s <| fun s ->
                Regex.And (r, s)
                |> cont

        (* These extended patterns can be rewritten using the simple patterns. *)
        | ExtendedRegex.OneOrMore r ->
            ExtendedRegex.ToRegexImpl r <| fun r ->
                // Rewrite r+ as rr*
                Regex.Concat (r, Regex.Star r)
                |> cont

        | ExtendedRegex.Optional r ->
            ExtendedRegex.ToRegexImpl r <| fun r ->
                // Rewrite r? as (|r)
                Regex.Concat (Regex.Epsilon, r)
                |> cont

        | ExtendedRegex.Repetition (r, m, n) ->
            // If not specified, the lower bound defaults to zero (0).
            let m = defaultArg m GenericZero
            raise <| System.NotImplementedException "ToRegexImpl"

    /// Simplifies an ExtendedRegex into a Regex.
    static member ToRegex (extRegex : ExtendedRegex) : Regex =
        ExtendedRegex.ToRegexImpl extRegex id
 
