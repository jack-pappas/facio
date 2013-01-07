(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

/// This is a TEMPORARY module which contains an example specification
/// to test the FSharpYacc compiler. This module should be deleted once
/// the compiler works correctly and we finish the lexer/parser modules!
module internal FSharpYacc.TestSpec

open Graham.Grammar
open Graham.Analysis
open FSharpYacc.Ast


let private ``fslex parser header`` =
    "(* (c) Microsoft Corporation 2005-2008.  *)\
    \
open FSharp.PowerPack.FsLex\
open FSharp.PowerPack.FsLex.AST\
"

let private ``fslex productions`` =
    let spec =
        [   {   ImpersonatedPrecedence = None;
                Symbols =
                    List.rev ["codeopt"; "Macros"; "RULE"; "Rules"; "codeopt"];
                Action =
                    Some " { TopCode = $1; Macros = $2; Rules = $4; BottomCode = $5; } "; }
        ] |> List.rev

    let codeopt =
        [   {   ImpersonatedPrecedence = None;
                Symbols = ["CODE"];
                Action =
                    Some "$1"; };
            {   ImpersonatedPrecedence = None;
                Symbols = [];
                Action =
                    Some "\"\", (fst parseState.ResultRange)"; };
        ] |> List.rev

    let Macros =
        [   {   ImpersonatedPrecedence = None;
                Symbols = [];
                Action =
                    Some "[]"; };
            {   ImpersonatedPrecedence = None;
                Symbols =
                    List.rev ["macro"; "Macros"];
                Action =
                    Some "$1 :: $2"; };
        ] |> List.rev

    let macro =
        [   {   ImpersonatedPrecedence = None;
                Symbols =
                    List.rev ["LET"; "IDENT"; "EQUALS"; "regexp"];
                Action =
                    Some "($2, $4)"; };
        ] |> List.rev

    let Rules =
        [   {   ImpersonatedPrecedence = None;
                Symbols =
                    List.rev ["rule"; "AND"; "Rules"];
                Action =
                    Some "$1 :: $3"; };
            {   ImpersonatedPrecedence = None;
                Symbols = ["rule"];
                Action =
                    Some "[$1]"; };
        ] |> List.rev

    let rule =
        [   {   ImpersonatedPrecedence = None;
                Symbols = [];
                Action =
                    Some "($1, $2, $6)"; };
        ] |> List.rev

    let args =
        [   {   ImpersonatedPrecedence = None;
                Symbols = [];
                Action =
                    Some "[]"; };
            {   ImpersonatedPrecedence = None;
                Symbols = List.rev ["IDENT"; "args"];
                Action =
                    Some "$1 :: $2"; };
        ] |> List.rev

    let optbar =
        [   {   ImpersonatedPrecedence = None;
                Symbols = [];
                Action =
                    None; };
            {   ImpersonatedPrecedence = None;
                Symbols = ["BAR"];
                Action =
                    None; };
        ] |> List.rev

    let clauses =
        [   {   ImpersonatedPrecedence = None;
                Symbols =
                    List.rev ["clause"; "BAR"; "clauses"];
                Action =
                    Some "$1 :: $3"; };
            {   ImpersonatedPrecedence = None;
                Symbols = ["clause"];
                Action =
                    Some "[$1]"; };
        ] |> List.rev

    let clause =
        [   {   ImpersonatedPrecedence = None;
                Symbols =
                    List.rev ["regexp"; "CODE"];
                Action =
                    Some "$1, $2"; };
        ] |> List.rev

    let regexp =
        [   {   ImpersonatedPrecedence = None;
                Symbols = ["CHAR"];
                Action =
                    Some "Inp (Alphabet (EncodeChar $1))"; };
            {   ImpersonatedPrecedence = None;
                Symbols = ["UNICODE_CATEGORY"];
                Action =
                    Some "Inp (UnicodeCategory $1)"; };
            {   ImpersonatedPrecedence = None;
                Symbols = ["EOF"];
                Action =
                    Some "Inp (Alphabet Eof)"; };
            {   ImpersonatedPrecedence = None;
                Symbols = ["UNDERSCORE"];
                Action =
                    Some "Inp Any"; };
            {   ImpersonatedPrecedence = None;
                Symbols = ["STRING"];
                Action =
                    Some "Seq [ for n in 0 .. $1.Length - 1 -> Inp (Alphabet (EncodeChar $1.[n]))]"; };
            {   ImpersonatedPrecedence = None;
                Symbols = ["IDENT"];
                Action =
                    Some "Macro $1"; };
            {   ImpersonatedPrecedence = Some "regexp_seq";
                Symbols =
                    List.rev ["regexp"; "regexp"];
                Action =
                    Some "Seq [$1; $2]"; };
            {   ImpersonatedPrecedence = Some "regexp_plus";
                Symbols =
                    List.rev ["regexp"; "PLUS"];
                Action =
                    Some "Seq [$1; Star $1]"; };
            {   ImpersonatedPrecedence = Some "regexp_star";
                Symbols =
                    List.rev ["regexp"; "STAR"];
                Action =
                    Some "Star $1"; };
            {   ImpersonatedPrecedence = Some "regexp_opt";
                Symbols =
                    List.rev ["regexp"; "QMARK"];
                Action =
                    Some "Alt [Seq []; $1]"; };
            {   ImpersonatedPrecedence = Some "regexp_alt";
                Symbols =
                    List.rev ["regexp"; "BAR"; "regexp"];
                Action =
                    Some "Alt [$1; $3]"; };
            {   ImpersonatedPrecedence = None;
                Symbols =
                    List.rev ["LPAREN"; "regexp"; "RPAREN"];
                Action =
                    Some "$2"; };
            {   ImpersonatedPrecedence = None;
                Symbols =
                    List.rev ["LBRACK"; "charset"; "RBRACK"];
                Action =
                    Some "Alt [ for c in $2 -> Inp (Alphabet c) ]"; };
            {   ImpersonatedPrecedence = None;
                Symbols =
                    List.rev ["LBRACK"; "HAT"; "charset"; "RBRACK"];
                Action =
                    Some "Inp (NotCharSet $3)"; };
        ] |> List.rev

    let charset =
        [   {   ImpersonatedPrecedence = None;
                Symbols = ["CHAR"];
                Action =
                    Some "Set.singleton(EncodeChar $1)"; };
            {   ImpersonatedPrecedence = None;
                Symbols =
                    List.rev ["CHAR"; "DASH"; "CHAR"];
                Action =
                    Some "Set.ofSeq [ for c in $1 .. $3 -> EncodeChar c ]"; };
            {   ImpersonatedPrecedence = None;
                Symbols =
                    List.rev ["charset"; "charset"];
                Action =
                    Some "Set.union $1 $2"; };
        ] |> List.rev

    [   "spec", spec;
        "codeopt", codeopt;
        "Macros", Macros;
        "macro", macro;
        "Rules", Rules;
        "rule", rule;
        "args", args;
        "optbar", optbar;
        "clauses", clauses;
        "clause", clause;
        "regexp", regexp;
        "charset", charset;
    ] |> List.rev

let ``fslex parser spec`` = {
    Header = Some ``fslex parser header``;
    Footer = None;
    NonterminalDeclarations =
        [   "AST.Spec", "spec";
        ];
    TerminalDeclarations =
        [   None, List.rev ["EOF"; "BAR"; "DOT"; "PLUS"; "STAR"; "QMARK"; "EQUALS"; "UNDERSCORE"; "LBRACK"; "RBRACK"; "HAT"; "DASH"];
            None, List.rev ["RULE"; "PARSE"; "LET"; "AND"; "LPAREN"; "RPAREN"];
            Some "string", ["UNICODE_CATEGORY"];
            Some "char", ["CHAR"]
            Some "AST.Code", ["CODE"];
            Some "string", List.rev ["IDENT"; "STRING"];
        ];
    StartingProductions =
        [ "spec" ];
    Associativities =
        [   NonAssociative, ["regexp_plus"; "regexp_star"];
            NonAssociative, ["regexp_opt"];
            Left, ["regexp_seq"];
            Left, ["regexp_alt"];
            Left, ["BAR"];
        ];
    Productions =
        ``fslex productions``;
    }

