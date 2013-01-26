(*
Copyright (c) 2012-2013, Jack Pappas
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

(* TODO :   Add annotations for position information (i.e., position in the lexer
            definition file) to:
            -   CodeFragment
            -   Most cases in the Pattern type; some cases, like Epsilon and Empty,
                can't be explicity used in a lexer definition file so they don't have
                source positions.
            
            Create new type aliases 'MacroIdentifierWithPosition' and 'RuleIdentifierWithPosition',
            defined as (MacroIdentifier * SourcePosition) and (RuleIdentifier * SourcePosition),
            respectively. Modify the Specification record type to use these new aliases instead of
            MacroIdentifier and RuleIdentifier -- this allows us to keep position information for
            these identifiers (for emitting warnings/errors), but without actually making it part
            of the identifier type.

            We do NOT need to add a position annotation to RuleClause as previously thought,
            because the position information will already be containing within the Pattern instance. *)

/// A position within a source file (e.g., a lexer definition file).
[<Struct; CustomEquality; CustomComparison>]
type SourcePosition =
    /// The zero-based line number.
    val Line : uint32
    /// The zero-based column number.
    val Column : uint32

    //
    new (line, column) = {
        Line = line;
        Column = column;
        }

    /// Determines if two SourcePositions are equivalent.
    static member Equals (x : SourcePosition, y : SourcePosition) =
        x.Line = y.Line && x.Column = y.Column

    /// Compares two SourcePositions and returns an indication of their relative values.
    static member Compare (x : SourcePosition, y : SourcePosition) =
        match compare x.Line y.Line with
        | 0 ->
            compare x.Column y.Column
        | x -> x

    override this.GetHashCode () =
        (*  Most files will have fewer than 65535 lines and 65535 columns,
            so computing the hash code like this means we'll almost never
            have hash conflicts in practice. *)

        // Shift the line number up by 16 bits, implicitly chopping
        // off the top 16 bits of the value.
        (this.Line <<< 16)
        // Mask out the top 16 bits of the column value, then combine
        // the result with the truncated and up-shifted line number.
        &&& (this.Column &&& 0x0000ffffu)
        // Convert to a signed integer value. Note that this doesn't generate
        // any CPU instructions (it's effectively a no-op).
        |> int

    override this.Equals value =
        match value with
        | null -> false
        | :? SourcePosition as other ->
            SourcePosition.Equals (this, other)
        | _ ->
            invalidArg "value" "The value is not an instance of SourcePosition."

    override this.ToString () =
        this.Line.ToString ()
        + ", "
        + this.Column.ToString ()

    interface System.IEquatable<SourcePosition> with
        member this.Equals other =
            SourcePosition.Equals (this, other)

    interface System.IComparable with
        member this.CompareTo value =
            match value with
            | null -> 1
            | :? SourcePosition as other ->
                SourcePosition.Compare (this, other)
            | _ ->
                invalidArg "value" "The value is not an instance of SourcePosition."

    interface System.IComparable<SourcePosition> with
        member this.CompareTo other =
            SourcePosition.Compare (this, other)

/// Unique identifier for a pattern macro
/// defined by a lexer specification.
type MacroIdentifier = string

//
type MacroIdentifierWithPosition =
    (SourcePosition * SourcePosition) option * MacroIdentifier

/// <summary>A regular-expression-based pattern used to define patterns within the lexer.</summary>
/// <remarks>This is a regular expression extended with additional
/// operators (for convenience) and pattern macros.</remarks>
type Pattern =
    (* Regex cases *)
    /// The empty string.
    | Epsilon
    /// Kleene *-closure.
    /// The specified Pattern will be matched zero (0) or more times.
    | Star of Pattern
    /// Concatenation. A Pattern immediately followed by another Pattern.
    | Concat of Pattern * Pattern
    /// Choice between two regular expressions (i.e., boolean OR).
    | Or of Pattern * Pattern
    /// Boolean AND of two regular expressions.
    | And of Pattern * Pattern
    (* TODO :   The Xor pattern can be implemented easily by rewriting it with one of the identities:
                p XOR q => (p OR q) AND (NOT (p AND q))
                -- or --
                p XOR q => (p AND (NOT q)) OR ((NOT p) AND q) *)
//    /// Exclusive-OR (XOR) of two regular expressions.
//    | Xor of Pattern * Pattern

    (* Extensions *)
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
    /// Negation.
    | Negate of Pattern

    (* Macros *)
    /// Match a pattern specified by a pattern macro.
    | Macro of MacroIdentifier

    (* Symbols *)
    /// Any character.
    | Any
    /// A set of characters.
    | CharacterSet of CharSet

    (* NOTE : The following cases are special cases of CharacterSet. *)
    /// The empty language.
    | Empty
    /// A character.
    | Character of char
    /// Match a character belonging to a specific Unicode category.
    | UnicodeCategory of UnicodeCategory

    /// Returns a Pattern created by concatenating the Patterns in the specified list.
    [<CompiledName("ConcatenateList")>]
    static member concatList list =
        List.reduce (FuncConvert.FuncFromTupled Pattern.Concat) list

    /// Returns a Pattern created by concatenating the Patterns in the specified array.
    [<CompiledName("ConcatenateArray")>]
    static member concatArray array =
        Array.reduce (FuncConvert.FuncFromTupled Pattern.Concat) array

    /// Returns a Pattern created by combining the Patterns in the
    /// specified list together using the logical AND relation.
    [<CompiledName("AndList")>]
    static member andList list =
        List.reduce (FuncConvert.FuncFromTupled Pattern.And) list

    /// Returns a Pattern created by combining the Patterns in the
    /// specified array together using the logical AND relation.
    [<CompiledName("AndArray")>]
    static member andArray array =
        Array.reduce (FuncConvert.FuncFromTupled Pattern.And) array

    /// Returns a Pattern created by combining the Patterns in the
    /// specified list together using the logical OR relation.
    [<CompiledName("OrList")>]
    static member orList list =
        List.reduce (FuncConvert.FuncFromTupled Pattern.Or) list    

    /// Returns a Pattern created by combining the Patterns in the
    /// specified array together using the logical OR relation.
    [<CompiledName("OrArray")>]
    static member orArray array =
        Array.reduce (FuncConvert.FuncFromTupled Pattern.Or) array

    /// Creates a pattern which matches the given character.
    [<CompiledName("OfCharacter")>]
    static member ofChar c : Pattern =
        CharSet.singleton c
        |> CharacterSet

    /// Creates a pattern which matches any one character in the specified list.
    [<CompiledName("OfCharacterList")>]
    static member ofCharList list : Pattern =
        CharSet.ofList list
        |> CharacterSet

    /// <summary>Creates a pattern which matches any one character in the range
    /// specified by [<paramref name="lower"/>, <paramref name="upper"/>].</summary>
    [<CompiledName("OfCharacterRange")>]
    static member ofCharRange lower upper : Pattern=
        CharSet.ofRange lower upper
        |> CharacterSet

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

/// The name of a parameter of a lexer rule.
type ParameterName = string

//
type Rule = {
    /// Parameters of the rule.
    // These are specified by name only -- their types will be inferred
    // in the generated lexer code.
    // NOTE : This list should be in reverse order; that is, the 'head'
    // of the list should be the last (right-most) parameter of the rule.
    Parameters : ParameterName list;
    //
    // NOTE : This list should be in reverse order; that is, the 'head'
    // of the list should be the last (bottom-most) clause of the rule.
    Clauses : RuleClause list;
}

/// Unique identifier for a lexer rule.
type RuleIdentifier = string

//
type RuleIdentifierWithPosition =
    (SourcePosition * SourcePosition) option * RuleIdentifier

/// A complete specification of a lexer.
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
    Macros : (MacroIdentifierWithPosition * Pattern) list;
    //
    // NOTE : This is specified as a list (instead of a Map) so we
    // know the order in which the rules were specified and also so we can
    // emit error messages for rules with duplicate names.
    // NOTE : This list should be in reverse order; that is, the 'head'
    // of the list should be the last (bottom-most) rule defined in the lexer definition.
    Rules : (RuleIdentifierWithPosition * Rule) list;
}

//
[<Measure>] type RuleClauseIdx
//
type RuleClauseIndex = int<RuleClauseIdx>

