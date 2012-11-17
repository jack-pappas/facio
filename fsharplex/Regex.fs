(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpLex.Regex

open Collections


//
type CharacterClass =
    /// Matches the specified character (once).
    | Character of char
    /// Matches any character except for '\n'.
    | Any
    /// Matches one character from the specified set.
    | Set of CharSet
    /// Matches any one character, except for those in the specified set.
    | NegatedSet of CharSet
    /// Matches one character from the specified Unicode category.
    | UnicodeCategory of System.Globalization.UnicodeCategory
    /// Matches any one character, except for those in the specified Unicode category.
    | NegatedUnicodeCategory of System.Globalization.UnicodeCategory

/// An extended regular expression: the basic form plus cases
/// to handle optional and one-or-more patterns.
type ExtendedRegex<'Symbol> =
    /// An empty string.
    | Epsilon
    /// A symbol from the language's alphabet.
    | Symbol of 'Symbol
    /// Choice between two patterns.
    | Alternate of ExtendedRegex<'Symbol> * ExtendedRegex<'Symbol>
    /// A Regex immediately followed by another Regex.
    | Sequence of ExtendedRegex<'Symbol> * ExtendedRegex<'Symbol>
    /// The specified Regex is matched zero (0) or more times.
    /// This is the Star (*) operator in a regular expression.
    | ZeroOrMore of ExtendedRegex<'Symbol>
    /// The specified Regex is matched one (1) or more times.
    /// This is the Plus (+) operator in a regular expression.
    | OneOrMore of ExtendedRegex<'Symbol>
    /// The specified Regex is optionally matched (i.e., it will
    /// be matched zero (0) or one (1) times).
    /// This is the QuestionMark (?) operator in a regular expression.
    | Optional of ExtendedRegex<'Symbol>

/// The most basic, simplified form of a regular expression.
type Regex<'Symbol> =
    /// An empty string.
    | Epsilon
    /// A symbol from the language's alphabet.
    | Symbol of 'Symbol
    /// Choice between two patterns.
    | Alternate of Regex<'Symbol> * Regex<'Symbol>
    /// A Regex immediately followed by another Regex.
    | Sequence of Regex<'Symbol> * Regex<'Symbol>
    /// The specified Regex is matched zero (0) or more times.
    /// This is the Star (*) operator in a regular expression.
    | ZeroOrMore of Regex<'Symbol>

    //
    static member private FromExtendedRegexImpl (extRegex : ExtendedRegex<'Symbol>) cont =
        match extRegex with
        | ExtendedRegex.Epsilon ->
            cont Epsilon
        | ExtendedRegex.Symbol symbol ->
            Symbol symbol
            |> cont
        | ExtendedRegex.Alternate (a, b) ->
            Regex<_>.FromExtendedRegexImpl a <| fun a ->
            Regex<_>.FromExtendedRegexImpl b <| fun b ->
                Alternate (a, b)
                |> cont

        | ExtendedRegex.Sequence (a, b) ->
            Regex<_>.FromExtendedRegexImpl a <| fun a ->
            Regex<_>.FromExtendedRegexImpl b <| fun b ->
                Sequence (a, b)
                |> cont

        | ExtendedRegex.ZeroOrMore extRegex ->
            Regex<_>.FromExtendedRegexImpl extRegex <| fun regex ->
                ZeroOrMore regex
                |> cont

        (* These extended patterns can be rewritten using the simple patterns. *)
        | ExtendedRegex.OneOrMore extRegex ->
            Regex<_>.FromExtendedRegexImpl extRegex <| fun regex ->
                // Wrap the nested regex in a simple regex that matches it one or more times.
                Sequence (regex, ZeroOrMore regex)
                |> cont

        | ExtendedRegex.Optional extRegex ->
            Regex<_>.FromExtendedRegexImpl extRegex <| fun regex ->
                // Wrap the nested regex in a simple regex that matches it zero or one times.
                Alternate (Epsilon, regex)
                |> cont

    //
    static member FromExtendedRegex (extRegex : ExtendedRegex<'Symbol>) =
        Regex<_>.FromExtendedRegexImpl extRegex id


    (* TODO :   Implement a method Tokenize which accepts a seq<'Symbol> and tokenizes it
                using the Regex (without compiling the Regex to a NFA/DFA. This method could
                use the List monad internally to implement the nondeterminism. *)
    (* TODO :   Implement a method Generate which lazily generates a sequence containing all
                of the words accepted by this regular expression. *)

