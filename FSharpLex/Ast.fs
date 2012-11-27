(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpLex.Ast

open Regex

(* TODO :   Add an annotation for position information (i.e., position
            in the lexer source file) to the CodeFragment type;
            perhaps also add it to RuleClause for the Pattern field so
            we can provide warnings when a rule clause won't ever be matched.  *)


/// A fragment of F# code.
type CodeFragment = string

//
type RuleClause = {
    //
    Pattern : Regex<char>;
    //
    Action : CodeFragment;
}

//
type Rule = RuleClause list

//
type MacroIdentifier = string

//
type RuleIdentifier = string

//
type Specification = {
    //
    Header : CodeFragment;
    //
    Footer : CodeFragment;
    //
    Macros : Map<MacroIdentifier, Regex<char>>;
    //
    Rules : Map<RuleIdentifier, Rule>;
}

