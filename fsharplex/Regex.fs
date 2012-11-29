(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpLex.Regex

open OptimizedClosures
open SpecializedCollections


//
type CharacterSet =
    //
    | Empty
    /// Any character except for newline ('\n').
    | Any
    /// A character.
    | Character of char
    /// A set of characters.
    | Set of CharSet
    /// Characters in a Unicode category.
    | UnicodeCategory of System.Globalization.UnicodeCategory

/// <summary>A regular expression.</summary>
/// <remarks>This type includes some cases which are normally referred to as "extended"
/// regular expressions. However, only those cases which are still closed under boolean
/// operations are included here, so the lanugage it represents must still be a regular
/// language.</remarks>
type Regex =
    /// The empty string.
    | Epsilon
    /// A (possibly empty) set of characters.
    | CharacterSet of CharacterSet
    /// Concatenation. A Regex immediately followed by another Regex.
    | Concat of Regex * Regex
    /// Kleene *-closure.
    /// The specified Regex will be matched zero (0) or more times.
    | Star of Regex
    /// Choice between two regular expressions (i.e., boolean OR).
    | Or of Regex * Regex
    /// Boolean AND of two regular expressions.
    | And of Regex * Regex
    /// Negation.
    | Not of Regex

    //
    static member private IsNullableImpl regex cont =
        match regex with
        | Epsilon ->
            cont true
        | CharacterSet _ ->
            cont false
        | Concat (a, b)
        | And (a, b) ->
            // IsNullable(a) && IsNullable(b)
            Regex.IsNullableImpl a <| fun a ->
                if not a then false
                else
                    Regex.IsNullableImpl b cont
        | Star _ ->
            cont true
        | Or (a, b) ->
            // IsNullable(a) || IsNullable(b)
            Regex.IsNullableImpl a <| fun a ->
                if a then true
                else
                    Regex.IsNullableImpl b cont
        | Not regex ->
            Regex.IsNullableImpl regex (cont >> not)

    /// Determines if a specified Regex is 'nullable', i.e.,
    /// it accepts the empty string (epsilon).
    static member IsNullable (regex : Regex) =
        Regex.IsNullableImpl regex id

    //
    static member private DerivativeImpl (contains : FSharpFunc<'Symbol, 'Symbol, bool>) wrtSymbol regex cont =
        match regex with
        | Epsilon ->
            cont Empty
        | CharacterSet charSet ->
            raise <| System.NotImplementedException "DerivativeImpl"
//            if contains.Invoke (symbol, wrtSymbol) then Epsilon else Empty
//            |> cont
        | Concat (a, b) ->
            failwith "TODO"
        | Star regex ->
            failwith "TODO"
        | Or (a, b) ->
            failwith "TODO"
        | And (a, b) ->
            failwith "TODO"
        | Not regex ->
            failwith "TODO"

    /// Computes the derivative of a Regex with respect to a specified symbol.
    static member Derivative (contains : 'Symbol -> 'Symbol -> bool) symbol regex =
        let contains = FSharpFunc<_,_,_>.Adapt contains
        Regex.DerivativeImpl contains symbol regex id

    //
    static member private CanonicalizeImpl (regex : Regex) cont =
//        match regex with
//        | Or (x, y) ->
//            // 
        raise <| System.NotImplementedException "CanonicalizeImpl"

    //
    static member Canonicalize (regex : Regex) =
        Regex.CanonicalizeImpl regex id

    /// Determines if two Regexes are similar, i.e., if they're approximately equal.
    static member Similar (x : Regex) (y : Regex) =
        // Canonicalize the Regexes, then they can be compared using
        // the built-in structural equality relation.
        (Regex.Canonicalize x) = (Regex.Canonicalize y)

/// An extended regular expression: the basic form plus cases
/// to handle optional and one-or-more patterns.
type ExtendedRegex =
    /// An empty string.
    | Epsilon
    /// A symbol from the language's alphabet.
    | CharacterSet of CharacterSet
    /// A Regex immediately followed by another Regex.
    | Concat of ExtendedRegex * ExtendedRegex
    /// Kleene *-closure.
    /// The specified Regex will be matched zero (0) or more times.
    | Star of ExtendedRegex
    /// Choice between two regular expressions (i.e., boolean OR).
    | Or of ExtendedRegex * ExtendedRegex
    /// Boolean AND of two regular expressions.
    | And of ExtendedRegex * ExtendedRegex
    /// Negation.
    | Not of ExtendedRegex
    /// The specified Regex is matched one (1) or more times.
    /// This is the Plus (+) operator in a regular expression.
    | OneOrMore of ExtendedRegex
    /// The specified Regex is optionally matched (i.e., it will
    /// be matched zero (0) or one (1) times).
    /// This is the QuestionMark (?) operator in a regular expression.
    | Optional of ExtendedRegex

    //
    static member private ToRegexImpl (extRegex : ExtendedRegex) cont : Regex =
        match extRegex with
        | ExtendedRegex.Epsilon ->
            cont Regex.Epsilon
        | ExtendedRegex.CharacterSet set ->
            Regex.CharacterSet set
            |> cont

        | ExtendedRegex.Concat (a, b) ->
            ExtendedRegex.ToRegexImpl a <| fun a ->
            ExtendedRegex.ToRegexImpl b <| fun b ->
                Regex.Concat (a, b)
                |> cont

        | ExtendedRegex.Star extRegex ->
            ExtendedRegex.ToRegexImpl extRegex <| fun regex ->
                Regex.Star regex
                |> cont

        | ExtendedRegex.Or (a, b) ->
            ExtendedRegex.ToRegexImpl a <| fun a ->
            ExtendedRegex.ToRegexImpl b <| fun b ->
                Regex.Or (a, b)
                |> cont

        | ExtendedRegex.And (a, b) ->
            ExtendedRegex.ToRegexImpl a <| fun a ->
            ExtendedRegex.ToRegexImpl b <| fun b ->
                Regex.And (a, b)
                |> cont

        | ExtendedRegex.Not extRegex ->
            ExtendedRegex.ToRegexImpl extRegex <| fun regex ->
                Regex.Not regex
                |> cont

        (* These extended patterns can be rewritten using the simple patterns. *)
        | ExtendedRegex.OneOrMore extRegex ->
            ExtendedRegex.ToRegexImpl extRegex <| fun regex ->
                // Rewrite s+ as ss*
                Regex.Concat (regex, Regex.Star regex)
                |> cont

        | ExtendedRegex.Optional extRegex ->
            ExtendedRegex.ToRegexImpl extRegex <| fun regex ->
                // Rewrite s? as (|s)
                Regex.Concat (Regex.Epsilon, regex)
                |> cont

    /// Simplifies an ExtendedRegex into a Regex.
    static member ToRegex (extRegex : ExtendedRegex) : Regex =
        ExtendedRegex.ToRegexImpl extRegex id

