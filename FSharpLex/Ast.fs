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

/// <summary>A regular-expression-based pattern used to define patterns within the lexer.</summary>
/// <remarks>This is a regular expression extended with additional
/// operators (for convenience) and pattern macros.</remarks>
type Pattern =
    (* Regex cases *)
    /// The empty string.
    | Epsilon
    /// A set of characters.
    | CharacterSet of CharSet
    /// Negation.
    | Negate of Pattern
    /// Kleene *-closure.
    /// The specified Pattern will be matched zero (0) or more times.
    | Star of Pattern
    /// Concatenation. A Pattern immediately followed by another Pattern.
    | Concat of Pattern * Pattern
    /// Choice between two regular expressions (i.e., boolean OR).
    | Or of Pattern * Pattern
    /// Boolean AND of two regular expressions.
    | And of Pattern * Pattern

    (* Extensions *)
    /// The empty language.
    | Empty
    /// Any character.
    // NOTE : This actually represents *any* character; it is not the same as the '.' pattern
    // in a lexer definition ('.' represents any character _except_ for '\n').
    | Any
    /// A character.
    | Character of char
    /// The specified Pattern is matched one (1) or more times.
    /// This is the Plus (+) operator in a regular expression.
    | OneOrMore of Pattern
    /// The specified Pattern is optionally matched (i.e., it will
    /// be matched zero (0) or one (1) times).
    /// This is the QuestionMark (?) operator in a regular expression.
    | Optional of Pattern
    /// Match the specified Pattern at least
    /// 'm' times and at most 'n' times.
    /// This is the {} operator in a regular expression.
    | Repetition of Pattern * uint32 option * uint32 option

    (* Macros *)
    //
    | Macro of MacroIdentifier
    //
    | UnicodeCategory of System.Globalization.UnicodeCategory

    /// Creates a Pattern which matches a string.
    [<CompiledName("LiteralString")>]
    static member literalString (str : string) =
        // If the string is empty, return an Epsilon pattern; by definition,
        // Epsilon is the acceptance of the empty string.
        if str.Length < 1 then
            Pattern.Epsilon
        else
            (* Construct the pattern backwards (i.e., starting at the end of the string) *)
            let mutable pattern = Pattern.Character str.[str.Length - 1]

            // Loop backwards through the string to prepend the rest of the characters
            for i = str.Length - 2 downto 0 do
                pattern <-
                    Pattern.Concat (
                        Pattern.Character str.[i],
                        pattern)

            // Return the constructed pattern.
            pattern

    //
    [<CompiledName("ConcatenateList")>]
    static member concatList list =
        List.reduce (FuncConvert.FuncFromTupled Pattern.Concat) list

    //
    [<CompiledName("AndList")>]
    static member andList list =
        List.reduce (FuncConvert.FuncFromTupled Pattern.And) list

    //
    [<CompiledName("OrList")>]
    static member orList list =
        List.reduce (FuncConvert.FuncFromTupled Pattern.Or) list

    //
    [<CompiledName("ConcatenateArray")>]
    static member concatArray array =
        Array.reduce (FuncConvert.FuncFromTupled Pattern.Concat) array

    //
    [<CompiledName("AndArray")>]
    static member andArray array =
        Array.reduce (FuncConvert.FuncFromTupled Pattern.And) array

    //
    [<CompiledName("OrArray")>]
    static member orArray array =
        Array.reduce (FuncConvert.FuncFromTupled Pattern.Or) array

/// <summary>A pattern defined in some clause (case) of a lexer rule.</summary>
/// <remarks>
/// This type can be thought of as extending <see cref="Pattern" /> with additional
/// cases representing special patterns which can only appear by themselves; i.e.,
/// they cannot be combined with any other patterns.
/// </remarks>
type RuleClausePattern =
    /// A pattern.
    | Pattern of Pattern
    /// The end-of-file marker.
    | EndOfFile

/// A fragment of F# code.
type CodeFragment = string

/// A clause of a lexer rule.
type RuleClause = {
    /// The pattern matched by this clause.
    Pattern : RuleClausePattern;
    /// The semantic action to be executed when
    /// <see cref="Pattern"/> is matched by the lexer.
    Action : CodeFragment;
}

//
[<Measure>] type RuleClauseIdx
//
type RuleClauseIndex = int<RuleClauseIdx>

//
type Rule = {
    /// Parameters of the rule.
    // These are specified by name only -- their types will be inferred
    // in the generated lexer code.
    // NOTE : This list should be in reverse order; that is, the 'head'
    // of the list should be the last (right-most) parameter of the rule.
    Parameters : string list;
    //
    // NOTE : This list should be in reverse order; that is, the 'head'
    // of the list should be the last (bottom-most) clause of the rule.
    Clauses : RuleClause list;
}

//
type RuleIdentifier = string

//
type Specification = {
    //
    Header : CodeFragment option;
    //
    Footer : CodeFragment option;
    //
    // NOTE : This is specified as a list (instead of a Map) so we
    // know the order in which the macros were specified (necessary
    // for validating the specification).
    // NOTE : This list should be in reverse order; that is, the 'head'
    // of the list should be the last (bottom-most) macro defined in the lexer definition.
    Macros : (MacroIdentifier * Pattern) list;
    //
    Rules : Map<RuleIdentifier, Rule>;
    //
    StartRule : RuleIdentifier;
}

