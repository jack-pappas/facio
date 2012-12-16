(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

/// The types representing the fsharpyacc abstract syntax tree (AST).
namespace FSharpYacc.Ast

open FSharpYacc.Grammar


/// A fragment of F# code.
type CodeFragment = string

/// Uniquely identifies a symbol (a terminal or nonterminal)
/// within a parser specification.
type SymbolIdentifier = string

/// The declared type of a nonterminal.
// NOTE : At the moment, these are not parsed or validated in any way.
type DeclaredType = string

//
type ProductionRule = {
    /// The symbols matched by this production rule.
    // NOTE : This list is in reverse order from the way the symbols appear in the parser
    // specification file. I.e., the last (right-most) symbol is the head of the list.
    Symbols : SymbolIdentifier list;
    /// A semantic action to be executed when this rule is matched.
    Action : CodeFragment option;
    /// When set, the default associativity and precedence of this rule is overridden
    /// and the associativity and precedence of the specified symbol used instead.
    ImpersonatedPrecedence : SymbolIdentifier option;
}

/// A complete parser specification of a grammar.
type Specification = {
    //
    Header : CodeFragment option;
    //
    Footer : CodeFragment option;
    /// <summary>Explicit type declarations for grammar productions (nonterminals).</summary>
    /// <remarks>Type declarations (<c>%type</c>) are optional, so this list may not contain
    /// a declaration for each production.</remarks>
    // NOTE : This list is in reverse order from the way the declarations appear in the parser
    // specification file. I.e., the last (bottom-most) declaration is the head of the list.
    NonterminalDeclarations : (DeclaredType * SymbolIdentifier) list;
    //
    TerminalDeclarations : (DeclaredType option * SymbolIdentifier list) list;
    /// The starting production(s) of the grammar.
    /// Only nonterminals can be specified, and all nonterminals specified as starting
    /// productions must also have explicit type declarations.
    /// At least one (1) nonterminal must be specified;
    /// a Specification is invalid if this field is empty.
    StartingProductions : SymbolIdentifier list;
    /// Explicitly declared associativities of symbols (terminals and nonterminals).
    /// The precedences of the symbols in the grammar are implied by their ordering
    /// in this list.
    // NOTE : This list is in reverse order from the way the declarations appear in the parser
    // specification file. I.e., the last (bottom-most) declaration is the head of the list.
    // Note that the last (bottom-most) declaration has the highest precedence.
    Associativities : (Associativity * SymbolIdentifier list) list;
    /// The production rules of the grammar.
    Productions : (SymbolIdentifier * ProductionRule list) list;
}

