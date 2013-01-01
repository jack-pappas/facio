(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.Program

/// Assembly-level attributes specific to this assembly.
module private AssemblyInfo =
    open System.Reflection
    open System.Resources
    open System.Runtime.CompilerServices
    open System.Runtime.InteropServices
    open System.Security
    open System.Security.Permissions

    [<assembly: AssemblyTitle("FSharpYacc")>]
    [<assembly: AssemblyDescription("A 'yacc'-inspired parser-generator tool for F#.")>]
    [<assembly: NeutralResourcesLanguage("en-US")>]
    [<assembly: Guid("fc309105-ce95-46d1-8cb4-568fc6bea85c")>]

    (*  Makes internal modules, types, and functions visible
        to the test project so they can be unit-tested. *)
    #if DEBUG
    [<assembly: InternalsVisibleTo("FSharpYacc.Tests")>]
    #endif

    (* Dependency hints for Ngen *)
    [<assembly: DependencyAttribute("FSharp.Core", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System.ComponentModel.Composition", LoadHint.Always)>]

    // Appease the F# compiler
    do ()


// TEMP : Remove these 'open' declarations once the test specification is compiled correctly.
open Graham.Grammar
open Graham.Analysis
open FSharpYacc.Ast


//// TEST : Try to compile a real-world specification to make sure this tool works correctly.
//let ``fslex parser header`` =
//    "(* (c) Microsoft Corporation 2005-2008.  *)\
//    \
//open FSharp.PowerPack.FsLex\
//open FSharp.PowerPack.FsLex.AST\
//"
//
//let ``fslex productions`` =
//    let spec =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = ["codeopt"; "Macros"; "RULE"; "Rules"; "codeopt"];
//                Action =
//                    Some " { TopCode = $1; Macros = $2; Rules = $4; BottomCode = $5; } "; }
//        ]
//
//    let codeopt =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = ["CODE"];
//                Action =
//                    Some "$1"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = [];
//                Action =
//                    Some "\"\", (fst parseState.ResultRange)"; };
//        ]
//
//    let Macros =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = [];
//                Action =
//                    Some "[]"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["macro"; "Macros"];
//                Action =
//                    Some "$1 :: $2"; };
//        ]
//
//    let macro =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = ["LET"; "IDENT"; "EQUALS"; "regexp"];
//                Action =
//                    Some "($2, $4)"; };
//        ]
//
//    let Rules =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = ["rule"; "AND"; "Rules"];
//                Action =
//                    Some "$1 :: $3"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["rule"];
//                Action =
//                    Some "[$1]"; };
//        ]
//
//    let rule =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = [];
//                Action =
//                    Some "($1, $2, $6)"; };
//        ]
//
//    let args =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = [];
//                Action =
//                    Some "[]"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["IDENT"; "args"];
//                Action =
//                    Some "$1 :: $2"; };
//        ]
//
//    let optbar =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = [];
//                Action =
//                    None; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["BAR"];
//                Action =
//                    None; };
//        ]
//
//    let clauses =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = ["clause"; "BAR"; "clauses"];
//                Action =
//                    Some "$1 :: $3"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["clause"];
//                Action =
//                    Some "[$1]"; };
//        ]
//
//    let clause =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = ["regexp"; "CODE"];
//                Action =
//                    Some "$1, $2"; };
//        ]
//
//    let regexp =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = ["CHAR"];
//                Action =
//                    Some "Inp (Alphabet (EncodeChar $1))"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["UNICODE_CATEGORY"];
//                Action =
//                    Some "Inp (UnicodeCategory $1)"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["EOF"];
//                Action =
//                    Some "Inp (Alphabet Eof)"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["UNDERSCORE"];
//                Action =
//                    Some "Inp Any"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["STRING"];
//                Action =
//                    Some "Seq [ for n in 0 .. $1.Length - 1 -> Inp (Alphabet (EncodeChar $1.[n]))]"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["IDENT"];
//                Action =
//                    Some "Macro $1"; };
//            {   ImpersonatedPrecedence = Some "regexp_seq";
//                Symbols = ["regexp"; "regexp"];
//                Action =
//                    Some "Seq [$1; $2]"; };
//            {   ImpersonatedPrecedence = Some "regexp_plus";
//                Symbols = ["regexp"; "PLUS"];
//                Action =
//                    Some "Seq [$1; Star $1]"; };
//            {   ImpersonatedPrecedence = Some "regexp_star";
//                Symbols = ["regexp"; "STAR"];
//                Action =
//                    Some "Star $1"; };
//            {   ImpersonatedPrecedence = Some "regexp_opt";
//                Symbols = ["regexp"; "QMARK"];
//                Action =
//                    Some "Alt [Seq []; $1]"; };
//            {   ImpersonatedPrecedence = Some "regexp_alt";
//                Symbols = ["regexp"; "BAR"; "regexp"];
//                Action =
//                    Some "Alt [$1; $3]"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["LPAREN"; "regexp"; "RPAREN"];
//                Action =
//                    Some "$2"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["LBRACK"; "charset"; "RBRACK"];
//                Action =
//                    Some "Alt [ for c in $2 -> Inp (Alphabet c) ]"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["LBRACK"; "HAT"; "charset"; "RBRACK"];
//                Action =
//                    Some "Inp (NotCharSet $3)"; };
//        ]
//
//    let charset =
//        [   {   ImpersonatedPrecedence = None;
//                Symbols = ["CHAR"];
//                Action =
//                    Some "Set.singleton(EncodeChar $1)"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["CHAR"; "DASH"; "CHAR"];
//                Action =
//                    Some "Set.ofSeq [ for c in $1 .. $3 -> EncodeChar c ]"; };
//            {   ImpersonatedPrecedence = None;
//                Symbols = ["charset"; "charset"];
//                Action =
//                    Some "Set.union $1 $2"; };
//        ]
//
//    [   "spec", spec;
//        "codeopt", codeopt;
//        "Macros", Macros;
//        "macro", macro;
//        "Rules", Rules;
//        "rule", rule;
//        "args", args;
//        "optbar", optbar;
//        "clauses", clauses;
//        "clause", clause;
//        "regexp", regexp;
//        "charset", charset;
//    ]
//
//let ``fslex parser spec`` = {
//    Header = Some ``fslex parser header``;
//    Footer = None;
//    NonterminalDeclarations =
//        [ "AST.Spec", "spec"; ];
//    TerminalDeclarations =
//        [   None, ["EOF"; "BAR"; "DOT"; "PLUS"; "STAR"; "QMARK"; "EQUALS"; "UNDERSCORE"; "LBRACK"; "RBRACK"; "HAT"; "DASH"];
//            None, ["RULE"; "PARSE"; "LET"; "AND"; "LPAREN"; "RPAREN"];
//            Some "string", ["UNICODE_CATEGORY"];
//            Some "char", ["CHAR"]
//            Some "AST.Code", ["CODE"];
//            Some "string", ["IDENT"; "STRING"];
//        ];
//    StartingProductions =
//        ["spec"];
//    Associativities =
//        [   NonAssociative, ["regexp_plus"; "regexp_star"];
//            NonAssociative, ["regexp_opt"];
//            Left, ["regexp_seq"];
//            Left, ["regexp_alt"];
//            Left, ["BAR"];
//        ];
//    Productions =
//        ``fslex productions``;
//    }

// TODO : Test compilation and code generation for the test specification.
//
//


(* TEST : Recognition points *)
/// Grammar G1 from "Recursive Ascent-Descent Parsing" by Horspool
let G1 =
    let G1 =
        let A =
            [|  [| Terminal 'a'; Nonterminal 'B'; Terminal 'b'; Nonterminal 'C' |]; |]

        let B =
            [|  [| Nonterminal 'B'; Terminal 'b' |];
                [| Terminal 'b' |]; |]

        let C =
            [|  [| Nonterminal 'C'; Terminal 'c' |];
                [| Terminal 'c' |]; |]

        {
        Terminals =
            Set.ofArray [| 'a'; 'b'; 'c' |]
        Nonterminals =
            Set.ofArray [| 'A'; 'B'; 'C' |]
        Productions =
            Map.empty
            |> Map.add 'A' A
            |> Map.add 'B' B
            |> Map.add 'C' C;
        }

    // Augment the grammar.
    Grammar.Augment (G1, 'A')

//
let lr0 =
    Graham.LR.Lr0.createTable G1

//
match Graham.LR.Lalr1.upgrade (G1, lr0) with
| Choice2Of2 errMsg ->
    printfn "Error: %s" errMsg
| Choice1Of2 lalr1 ->
    //
    let freePositions =
        FreePositions.ofGrammar (G1, lalr1)

    //
    let recognitionPoints =
        RecognitionPoints.calculate freePositions

    //
    let earliestRecognitionPoints =
        RecognitionPoints.earliest recognitionPoints

    let wfowfe = "wofwoekf".Length + 10
    ()


printfn "Press any key to exit..."
System.Console.ReadKey ()
|> ignore
