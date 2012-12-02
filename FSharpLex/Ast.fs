(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpLex.Ast

open System.Globalization
open LanguagePrimitives
open SpecializedCollections
open Regex

(* TODO :   Add an annotation for position information (i.e., position
            in the lexer source file) to the CodeFragment type;
            perhaps also add it to RuleClause for the Pattern field so
            we can provide warnings when a rule clause won't ever be matched.  *)

//
type MacroIdentifier = string

//
[<RequireQualifiedAccess>]
module private Unicode =
    /// Maps each UnicodeCategory to the set of characters in the category.
    let categoryCharSet =
        // OPTIMIZE : If this takes "too long" to compute on-the-fly, we could pre-compute
        // the category sets and implement code which recreates the CharSets from the intervals
        // in the CharSets (not the individual values, which would be much slower).
        let table = System.Collections.Generic.Dictionary<_,_> (30)
        for i = 0 to 65535 do
            /// The Unicode category of this character.
            let category = System.Char.GetUnicodeCategory (char i)

            // Add this character to the set for this category.
            table.[category] <-
                match table.TryGetValue category with
                | true, charSet ->
                    CharSet.add (char i) charSet
                | false, _ ->
                    CharSet.singleton (char i)

        // TODO : Assert that the table contains an entry for every UnicodeCategory value.
        // Otherwise, exceptions will be thrown at run-time if we try to retrive non-existent entries.

        // Convert the dictionary to a Map
        (Map.empty, table)
        ||> Seq.fold (fun categoryMap kvp ->
            Map.add kvp.Key kvp.Value categoryMap)

/// <summary>A regular-expression-based pattern used to define patterns within the lexer.</summary>
/// <remarks>This is a regular expression extended with additional
/// operators (for convenience) and pattern macros.</remarks>
type LexerPattern =
    (* Regex cases *)
    /// The empty string.
    | Epsilon
    /// A set of characters.
    | CharacterSet of CharSet
    /// Negation.
    | Negate of LexerPattern
    /// Kleene *-closure.
    /// The specified LexerPattern will be matched zero (0) or more times.
    | Star of LexerPattern
    /// Concatenation. A LexerPattern immediately followed by another LexerPattern.
    | Concat of LexerPattern * LexerPattern
    /// Choice between two regular expressions (i.e., boolean OR).
    | Or of LexerPattern * LexerPattern
    /// Boolean AND of two regular expressions.
    | And of LexerPattern * LexerPattern

    (* Extensions *)
    /// The empty language.
    | Empty
    /// Any character except for newline ('\n').
    | Any
    /// A character.
    | Character of char
    /// The specified LexerPattern is matched one (1) or more times.
    /// This is the Plus (+) operator in a regular expression.
    | OneOrMore of LexerPattern
    /// The specified LexerPattern is optionally matched (i.e., it will
    /// be matched zero (0) or one (1) times).
    /// This is the QuestionMark (?) operator in a regular expression.
    | Optional of LexerPattern
    /// Match the specified LexerPattern at least
    /// 'm' times and at most 'n' times.
    /// This is the {} operator in a regular expression.
    | Repetition of LexerPattern * uint32 option * uint32 option

    (* Macros *)
    //
    | Macro of MacroIdentifier
    //
    | UnicodeCategory of System.Globalization.UnicodeCategory

    //
    static member private ToRegexImpl (extRegex : LexerPattern) cont : Regex =
        match extRegex with
        | Epsilon ->
            cont Regex.Epsilon        
        | CharacterSet charSet ->
            Regex.CharacterSet charSet
            |> cont
        | Negate r ->
            LexerPattern.ToRegexImpl r <| fun r ->
                Regex.Negate r
                |> cont
        | Star r ->
            LexerPattern.ToRegexImpl r <| fun r ->
                Regex.Star r
                |> cont
        | Concat (r, s) ->
            LexerPattern.ToRegexImpl r <| fun r ->
            LexerPattern.ToRegexImpl s <| fun s ->
                Regex.Concat (r, s)
                |> cont
        | Or (r, s) ->
            LexerPattern.ToRegexImpl r <| fun r ->
            LexerPattern.ToRegexImpl s <| fun s ->
                Regex.Or (r, s)
                |> cont
        | And (r, s) ->
            LexerPattern.ToRegexImpl r <| fun r ->
            LexerPattern.ToRegexImpl s <| fun s ->
                Regex.And (r, s)
                |> cont

        (* These extended patterns can be rewritten using the simple patterns. *)
        | Empty ->
            Regex.CharacterSet CharSet.empty
            |> cont
        | Any ->
            cont Regex.Any
        | Character c ->
            Regex.Character c
            |> cont
        | OneOrMore r ->
            LexerPattern.ToRegexImpl r <| fun r ->
                // Rewrite r+ as rr*
                Regex.Concat (r, Regex.Star r)
                |> cont
        | Optional r ->
            LexerPattern.ToRegexImpl r <| fun r ->
                // Rewrite r? as (|r)
                Regex.Concat (Regex.Epsilon, r)
                |> cont
        | Repetition (r, m, n) ->
            // If not specified, the lower bound defaults to zero (0).
            let m = defaultArg m GenericZero
            raise <| System.NotImplementedException "ToRegexImpl"

        (* Simplify the macro patterns. *)
        | Macro macroId ->
            raise <| System.NotImplementedException "ToRegexImpl"
        | UnicodeCategory unicodeCategory ->
            raise <| System.NotImplementedException "ToRegexImpl"

    /// Simplifies an LexerPattern into a Regex.
    static member ToRegex (extRegex : LexerPattern) : Regex =
        LexerPattern.ToRegexImpl extRegex id


/// A fragment of F# code.
type CodeFragment = string

//
type RuleClause = {
    //
    Pattern : LexerPattern;
    //
    Action : CodeFragment;
}

//
[<Measure>] type RuleClauseIdx
//
type RuleClauseIndex = int<RuleClauseIdx>

//
type Rule = RuleClause list

//
type RuleIdentifier = string

//
type Specification = {
    //
    Header : CodeFragment option;
    //
    Footer : CodeFragment option;
    //
    Macros : Map<MacroIdentifier, LexerPattern>;
    //
    Rules : Map<RuleIdentifier, Rule>;
}

