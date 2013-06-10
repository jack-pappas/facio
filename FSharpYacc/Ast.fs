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

/// The types representing the fsharpyacc abstract syntax tree (AST).
namespace FSharpYacc.Ast

open System.Diagnostics
open Graham


/// A fragment of F# code.
type CodeFragment = string

/// Uniquely identifies a nonterminal within a parser specification.
type NonterminalIdentifier = string

/// Uniquely identifies a terminal within a parser specification.
type TerminalIdentifier = string

/// Uniquely identifies a symbol (either a terminal
/// or a nonterminal) within a parser specification.
type SymbolIdentifier = string

/// The declared type of a nonterminal.
// NOTE : At the moment, these are not parsed or validated in any way.
type DeclaredType = string

//
[<DebuggerDisplay("{DebuggerDisplay,nq}")>]
type ProductionRule = {
    /// The symbols matched by this production rule.
    // NOTE : This list is in reverse order from the way the symbols appear in the parser
    // specification file. I.e., the last (right-most) symbol is the head of the list.
    Symbols : SymbolIdentifier list;
    /// A semantic action to be executed when this rule is matched.
    Action : CodeFragment option;
    /// When set, the default associativity and precedence of this rule is overridden
    /// and the associativity and precedence of the specified terminal used instead.
    /// The specified terminal may be a "dummy" token which is used only for the purposes
    /// of conveying associativity and precedence.
    ImpersonatedPrecedence : TerminalIdentifier option;
} with
    /// Private. For use with DebuggerDisplayAttribute only.
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private this.DebuggerDisplay
        with get () =
            match this.Symbols with
            | [] -> "(Empty)"
            | symbols ->
                System.String.Join (" ", List.toArray symbols)

/// <summary>A complete parser specification of a grammar.</summary>
/// <remarks>All lists used within this record are in reverse order compared to their
/// order in the parser specification file.</remarks>
type Specification = {
    //
    Header : CodeFragment option;
    //
    Footer : CodeFragment option;
    /// <summary>Explicit type declarations for grammar productions (nonterminals).</summary>
    /// <remarks>Type declarations (<c>%type</c>) are optional, so this list may not contain
    /// a declaration for each production.</remarks>
    NonterminalDeclarations : (DeclaredType * NonterminalIdentifier) list;
    //
    TerminalDeclarations : (DeclaredType option * TerminalIdentifier list) list;
    /// The starting production(s) of the grammar.
    /// Only nonterminals can be specified, and all nonterminals specified as starting
    /// productions must also have explicit type declarations.
    /// At least one (1) nonterminal must be specified;
    /// a Specification is invalid if this field is empty.
    StartingProductions : NonterminalIdentifier list;   // TODO : Add position information
    /// <summary>Explicitly declared associativities of terminals. This includes 'dummy'
    /// terminals created by %prec declarations in production rules.</summary>
    /// <remarks>
    /// <para>Terminal precedences are implied from their ordering in this list. The list is given in
    /// order of _decreasing_ precedence; that is, the head of the list has the highest precedence.</para>
    /// <para>The precedence of production rules is defined as the precedence of the last (right-most)
    /// terminal, or the precedence of the terminal specified by the %prec declaration (if present).
    /// Note that not all production rules will be assigned a precedence value.</para>
    /// </remarks>
    Associativities : (Associativity * TerminalIdentifier list) list;
    /// The production rules of the grammar.
    Productions : (NonterminalIdentifier * ProductionRule list) list;
}

