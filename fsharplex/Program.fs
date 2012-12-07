(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpLex.Program

open Graph
open Regex

//
module internal AssemblyInfo =
    open System.Reflection
    open System.Resources
    open System.Runtime.CompilerServices
    open System.Runtime.InteropServices
    open System.Security
    open System.Security.Permissions

    [<assembly: AssemblyTitle("FSharpLex")>]
    [<assembly: AssemblyDescription("A 'lex'-inspired lexical-analyzer-generator tool for F#.")>]
    [<assembly: NeutralResourcesLanguage("en-US")>]
    [<assembly: Guid("3e878e31-5c9a-456d-9ab8-a12e3fed1efe")>]

    (*  Makes internal modules, types, and functions visible
        to the test project so they can be unit-tested. *)
    #if DEBUG
    [<assembly: InternalsVisibleTo("FSharpLex.Tests")>]
    #endif

    (* Dependency hints for Ngen *)
    [<assembly: DependencyAttribute("FSharp.Core", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System.ComponentModel.Composition", LoadHint.Always)>]

    // Appease the F# compiler
    do ()


open SpecializedCollections
open Ast


//
let private ofCharList list =
    CharSet.ofList list
    |> LexerPattern.CharacterSet


// TEST : Try compiling a more-complex test specification.
let ``fslex header`` =
    @"(* (c) Microsoft Corporation 2005-2008.  *)
  
module internal FSharpx.Text.Lexing.FsLex.Lexer

open FSharpx.Text.Lexing.FsLex.Ast
open FSharpx.Text.Lexing.FsLex.Parser
open FSharpx.Text.Lexing
open System.Text


let private escape = function
    | '\\' -> '\\'
    | '\'' -> '\''
    | 'n' -> '\n'
    | 't' -> '\t'
    | 'b' -> '\b'
    | 'r' -> '\r'
    | c -> c

let inline private lexeme (lexbuf : LexBuffer<char>) =
    LexBuffer<_>.LexemeString lexbuf

let private newline (lexbuf : LexBuffer<_>) =
    lexbuf.EndPos <- Position.nextLine lexbuf.EndPos

let private unexpected_char lexbuf =
    let msg = sprintf ""Unexpected character '%s'"" (lexeme lexbuf)
    raise <| exn msg

let private digit d =
    if d >= '0' && d <= '9' then
        int32 d - int32 '0'
    else
        failwith ""digit""

let private hexdigit d =
    if d >= '0' && d <= '9' then digit d
    elif d >= 'a' && d <= 'f' then int32 d - int32 'a' + 10
    elif d >= 'A' && d <= 'F' then int32 d - int32 'A' + 10
    else failwithf ""bad hexdigit: %c"" d

let private trigraph c1 c2 c3 =
      char (digit c1 * 100 + digit c2 * 10 + digit c3)

let private hexgraph c1 c2 =
    char (hexdigit c1 * 16 + hexdigit c2)

let private unicodegraph_short (s : string) =
    if s.Length <> 4 then
        failwith ""unicodegraph""

    char <| hexdigit s.[0] * 4096 + hexdigit s.[1] * 256 + hexdigit s.[2] * 16 + hexdigit s.[3]

let private unicodegraph_long (s : string) =
    if s.Length <> 8 then
        failwith ""unicodegraph_long""

    let high = hexdigit s.[0] * 4096 + hexdigit s.[1] * 256 + hexdigit s.[2] * 16 + hexdigit s.[3]
    let low = hexdigit s.[4] * 4096 + hexdigit s.[5] * 256 + hexdigit s.[6] * 16 + hexdigit s.[7]
    if high = 0 then
        None, char low
    else
      (* A surrogate pair - see http:/ /www.unicode.org/unicode/uni2book/ch03.pdf, section 3.7 *)
      Some (
        char (0xD800 + ((high * 0x10000 + low - 0x10000) / 0x400))),
        char (0xDF30 + ((high * 0x10000 + low - 0x10000) % 0x400))

"

let ``fslex macros`` =
    let letter =
        // ['A'-'Z'] | ['a'-'z']
        LexerPattern.Or (
            CharacterSet <| CharSet.ofRange 'A' 'Z',
            CharacterSet <| CharSet.ofRange 'a' 'z')

    let digit =
        // ['0'-'9']
        CharacterSet <| CharSet.ofRange '0' '9'

    let whitespace =
        // [' ' '\t']
        Or (Character ' ',
            Character '\t')

    let char =
        // '\'' ( [^'\\'] | ('\\' ( '\\' | '\'' | "\"" | 'n' | 't' | 'b' | 'r'))) '\''
        Concat (
            Character '\'',
            Concat (
                Or (Negate (Character '\''),
                    Concat (
                        Character '\\',
                        ofCharList ['\\' ; '\'' ; '"' ; 'n' ; 't' ; 'b' ; 'r'])),
                Character '\''))

    let hex =
        // ['0'-'9'] | ['A'-'F'] | ['a'-'f']
        LexerPattern.orArray [|
            CharacterSet <| CharSet.ofRange '0' '9';
            CharacterSet <| CharSet.ofRange 'A' 'F';
            CharacterSet <| CharSet.ofRange 'a' 'f';
        |]

    let hexgraph =
        // '\\' 'x' hex hex
        LexerPattern.concatArray [|
            Character '\\';
            Character 'x';
            Macro "hex";
            Macro "hex";
        |]

    let trigraph =
        // '\\' digit digit digit
        LexerPattern.concatArray [|
            Character '\\';
            Macro "digit";
            Macro "digit";
            Macro "digit";
        |]

    let newline =
        // ('\n' | '\r' '\n')
        Or (Character '\n',
            Concat (Character '\r',
                    Character '\n'))

    let ident_start_char =
        // letter
        Macro "letter"

    let ident_char =
        // ident_start_char | digit | ['\'' '_']
        LexerPattern.orArray [|
            Macro "ident_start_char";
            Macro "digit";
            CharacterSet <| CharSet.ofList ['\''; '_']
            |]

    let ident =
        // ident_start_char ident_char*
        Concat (
            Macro "ident_start_char",
            Star <| Macro "ident_char")

    let unicodegraph_short =
        // '\\' 'u' hex hex hex hex
        LexerPattern.concatArray [|
            Character '\\';
            Character 'u';
            Macro "hex";
            Macro "hex";
            Macro "hex";
            Macro "hex";
            |]

    let unicodegraph_long =
        // '\\' 'U' hex hex hex hex hex hex hex hex
        LexerPattern.concatArray [|
            Character '\\';
            Character 'U';
            Macro "hex";
            Macro "hex";
            Macro "hex";
            Macro "hex";
            Macro "hex";
            Macro "hex";
            Macro "hex";
            Macro "hex";
            |]

    [   "letter", letter;
        "digit", digit;
        "whitespace", whitespace;
        "char", char;
        "hex", hex;
        "hexgraph", hexgraph;
        "trigraph", trigraph;
        "newline", newline;
        "ident_start_char", ident_start_char;
        "ident_char", ident_char;
        "ident", ident;
        "unicodegraph_short", unicodegraph_short;
        "unicodegraph_long", unicodegraph_long; ]
    // Reverse the list before returning, because it's expected to be in reverse order.
    |> List.rev

let ``fslex rules`` =
    Map.empty
    |> Map.add "token" {
        Parameters = List.empty;
        Clauses =
            List.rev [
                {   Pattern = LexerPattern.literalString "rule";
                    Action =
                        "        RULE"; };

                {   Pattern = LexerPattern.literalString "parse";
                    Action =
                        "        PARSE"; };

                {   Pattern = LexerPattern.literalString "eof";
                    Action =
                        "        EOF"; };

                {   Pattern = LexerPattern.literalString "let";
                    Action =
                        "        LET"; };

                {   Pattern = LexerPattern.literalString "and";
                    Action =
                        "        AND"; };

                {   Pattern = Macro "char";
                    Action =
                        "        let s = lexeme lexbuf\r\n        CHAR (if s.[1] = '\\\\' then escape s.[2] else s.[1])"; };

                {   Pattern =
                        LexerPattern.concatArray [|
                            Character '\'';
                            Macro "trigraph";
                            Character '\'';
                            |];
                    Action =
                        "        let s = lexeme lexbuf\r\n        CHAR (trigraph s.[2] s.[3] s.[4])"; };

                {   Pattern =
                        LexerPattern.concatArray [|
                            Character '\'';
                            Macro "hexgraph";
                            Character '\'';
                            |];
                    Action =
                        "        let s = lexeme lexbuf\r\n        CHAR (hexgraph s.[3] s.[4])"; };

                {   Pattern =
                        LexerPattern.concatArray [|
                            Character '\'';
                            Macro "unicodegraph_short";
                            Character '\'';
                            |];
                    Action =
                        "        let s = lexeme lexbuf\r\n        CHAR (unicodegraph_short s.[3..6])"; };

                {   Pattern =
                        LexerPattern.concatArray [|
                            Character '\'';
                            Macro "unicodegraph_long";
                            Character '\'';
                            |];
                    Action =
                        "        let s = lexeme lexbuf\r\n        match unicodegraph_long s.[3..10] with\r\n        | None, c -> CHAR c\r\n        | Some _ , _ -> failwith \"Unicode characters needing surrogate pairs are not yet supported by this tool.\""; };

                {   Pattern =
                        LexerPattern.concatArray [|
                            Character '\'';
                            Character '\\';
                            CharacterSet <| CharSet.ofRange 'A' 'Z';
                            CharacterSet <| CharSet.ofRange 'a' 'z';
                            Character '\'';                        
                            |];
                    Action =
                        "        let s = (lexeme lexbuf).[2..3]\r\n        UNICODE_CATEGORY s"; };

                {   Pattern = Character '{';
                    Action =
                        "        let p = lexbuf.StartPos\r\n        let buff = StringBuilder 100\r\n        // adjust the first line to get even indentation for all lines w.r.t. the left hand margin\r\n        buff.Append (String.replicate (lexbuf.StartPos.Column + 1) \" \") |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern = Character '"';
                    Action =
                        "        string lexbuf.StartPos (StringBuilder 100) lexbuf"; };

                {   Pattern = OneOrMore (Macro "whitespace");
                    Action =
                        "        token lexbuf"; };

                {   Pattern = Macro "newline";
                    Action =
                        "        newline lexbuf\r\n        token lexbuf"; };

                {   Pattern =
                        Concat (
                            Macro "ident_start_char",
                            Star (Macro "ident_char"));
                    Action =
                        "        IDENT (lexeme lexbuf)"; };

                {   Pattern = Character '|';
                    Action =
                        "        BAR"; };

                {   Pattern = Character '.';
                    Action =
                        "        DOT"; };

                {   Pattern = Character '+';
                    Action =
                        "        PLUS"; };

                {   Pattern = Character '*';
                    Action =
                        "        STAR"; };

                {   Pattern = Character '?';
                    Action =
                        "        QMARK"; };

                {   Pattern = Character '=';
                    Action =
                        "        EQUALS"; };

                {   Pattern = Character '[';
                    Action =
                        "        LBRACK"; };

                {   Pattern = Character ']';
                    Action =
                        "        RBRACK"; };

                {   Pattern = Character '(';
                    Action =
                        "        LPAREN"; };

                {   Pattern = Character ')';
                    Action =
                        "        RPAREN"; };

                {   Pattern = Character '_';
                    Action =
                        "        UNDERSCORE"; };

                {   Pattern = Character '^';
                    Action =
                        "        HAT"; };

                {   Pattern = Character '-';
                    Action =
                        "        DASH"; };

                {   Pattern = LexerPattern.literalString "(*";
                    Action =
                        "        comment lexbuf.StartPos lexbuf\r\n        |> ignore\r\n        token lexbuf"; };

                {   Pattern =
                        Concat (
                            LexerPattern.literalString "//",
                            Star (Negate (CharacterSet <| CharSet.ofList ['\n'; '\r'])));
                    Action =
                        "        token lexbuf"; };

                {   Pattern = Any;
                    Action =
                        "        unexpected_char lexbuf"; };

                // TODO : How to represent the end-of-file marker?
                {   Pattern = Empty;
                    Action =
                        "        EOF"; };
                ]; }

     |> Map.add "string" {
        Parameters = ["buff"; "p"];
        Clauses =
            List.rev [
                {   Pattern =
                        Concat (
                            Character '\\',
                            Macro "newline");
                    Action =
                        "        newline lexbuf\r\n        string p buff lexbuf"; };

                {   Pattern =
                        Concat (
                            Character '\\',
                            CharacterSet <| CharSet.ofList ['"' ; '\\' ; '\'' ; 'n' ; 't' ; 'b' ; 'r']);
                    Action =
                        "        buff.Append (escape (lexeme lexbuf).[1]) |> ignore\r\n        string p buff lexbuf"; };

                {   Pattern = Macro "trigraph";
                    Action =
                        "        let s = lexeme lexbuf\r\n        trigraph s.[1] s.[2] s.[3]\r\n        |> buff.Append\r\n        |> ignore\r\n        string p buff lexbuf"; };

                {   Pattern = Character '"';
                    Action =
                        "        STRING <| buff.ToString ()"; };

                {   Pattern = Macro "newline";
                    Action =
                        "        newline lexbuf\r\n        buff.AppendLine () |> ignore\r\n        string p buff lexbuf"; };

                {   Pattern =
                        OneOrMore (
                            LexerPattern.orArray [|
                                Macro "whitespace";
                                Macro "letter";
                                Macro "digit";
                                |]);
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        string p buff lexbuf"; };

                // TODO : How to represent the end-of-file marker?
                {   Pattern = Empty;
                    Action =
                        "        let msg = sprintf \"End of file in string started at (%d,%d).\" p.pos_lnum (p.pos_cnum - p.pos_bol)\r\n        raise <| exn msg"; };

                {   Pattern = Any;
                    Action =
                        "        buff.Append (lexeme lexbuf).[0] |> ignore\r\n        string p buff lexbuf"; };
                ]; }

     |> Map.add "code" {
        Parameters = ["buff"; "p"];
        Clauses =
            List.rev [
                {   Pattern =
                        LexerPattern.literalString "}";
                    Action =
                        "        CODE (buff.ToString (), p)"; };

                {   Pattern =
                        LexerPattern.literalString "{";
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        code p buff lexbuf |> ignore\r\n        buff.Append \"}\" |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern =
                        Concat (
                            Character '\\',
                            Or (Character '"', Character '\\'));
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern = LexerPattern.literalString "\"";
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        codestring buff lexbuf |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern = Macro "newline";
                    Action =
                        "        newline lexbuf\r\n        buff.AppendLine () |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern =
                        OneOrMore (
                            LexerPattern.orArray [|
                                Macro "whitespace";
                                Macro "letter";
                                Macro "digit";
                                |]);
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern =
                        Concat (
                            LexerPattern.literalString "//",
                            Star (Negate (CharacterSet <| CharSet.ofList ['\n'; '\r'])));
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        code p buff lexbuf"; };

                // TODO : How to represent the end-of-file marker?
                {   Pattern = Empty;
                    Action =
                        "        EOF"; };

                {   Pattern = Any;
                    Action =
                        "        buff.Append (lexeme lexbuf).[0] |> ignore\r\n        code p buff lexbuf"; };
                ]; }

     |> Map.add "codestring" {
        Parameters = ["buff"];
        Clauses =
            List.rev [
                {   Pattern =
                        Concat (
                            Character '\\',
                            Or (Character '"', Character '\\'));
                    Action = "        buff.Append (lexeme lexbuf) |> ignore\r\n        codestring buff lexbuf"; };

                {   Pattern = Character '"';
                    Action = "        buff.Append (lexeme lexbuf) |> ignore\r\n        buff.ToString ()"; };

                {   Pattern = Macro "newline";
                    Action = "        newline lexbuf\r\n        buff.AppendLine () |> ignore\r\n        codestring buff lexbuf"; };

                {   Pattern =
                        OneOrMore (
                            LexerPattern.orArray [|
                                Macro "whitespace";
                                Macro "letter";
                                Macro "digit";
                                |]);
                    Action = "        buff.Append (lexeme lexbuf) |> ignore\r\n        codestring buff lexbuf"; };

                // TODO : How to handle the end-of-file marker?
                {   Pattern = Empty;
                    Action = "        failwith \"Unterminated string in code.\""; };

                {   Pattern = Any;
                    Action = "        buff.Append (lexeme lexbuf).[0] |> ignore\r\n        codestring buff lexbuf"; };
                ]; }

     |> Map.add "comment" {
        Parameters = ["p"];
        Clauses =
            List.rev [
                {   Pattern = Macro "char";
                    Action = "        comment p lexbuf"; };

                {   Pattern = Character '"';
                    Action = "        try string lexbuf.StartPos (StringBuilder 100) lexbuf\r\n        with Failure s ->\r\n            let msg = s + System.Environment.NewLine + sprintf \"Error while processing string nested in comment started at (%d,%d).\" p.pos_lnum (p.pos_cnum - p.pos_bol)\r\n            raise <| exn msg\r\n        |> ignore\r\n        comment p lexbuf"; };

                {   Pattern = LexerPattern.literalString "(*";
                    Action = "        try comment p lexbuf\r\n        with Failure s ->\r\n            let msg = s + System.Environment.NewLine + sprintf \"Error while processing nested comment started at (%d,%d).\" p.pos_lnum (p.pos_cnum - p.pos_bol)\r\n            raise <| exn msg\r\n        |> ignore\r\n        comment p lexbuf"; };

                {   Pattern = Macro "newline";
                    Action = "        newline lexbuf\r\n        comment p lexbuf"; };

                {   Pattern = LexerPattern.literalString "*)";
                    Action = "        ()"; };

                // TODO : How to handle the end-of-file marker?
                {   Pattern = Empty;
                    Action = "        let msg = sprintf \"End of file in comment started at (%d,%d).\" p.pos_lnum (p.pos_cnum - p.pos_bol)\r\n        raise <| exn msg"; };

                {   Pattern =
                        OneOrMore (
                            Negate (
                                CharacterSet <| CharSet.ofList ['\''; '('; '*'; '\n'; '\r'; '"'; ')']));
                    Action = "        comment p lexbuf"; };

                {   Pattern = Any;
                    Action = "        comment p lexbuf"; };
                ]; }

let ``fslex specification`` = {
    Header = Some ``fslex header``;
    Footer = None;
    Macros = ``fslex macros``;
    Rules = ``fslex rules``;
    StartRule = "token"; }

let options : Compile.CompilationOptions = {
    Unicode = false; }

let ``compiled fslex spec`` =
    Compile.lexerSpec ``fslex specification`` options

match ``compiled fslex spec`` with
| Choice2Of2 errors ->
    errors
    |> Array.iter System.Console.WriteLine
| Choice1Of2 compiledTestSpec ->
    let generatedCode = CodeGen.generateString compiledTestSpec options
    //GraphGen.Dgml.emitSeparate compiledTestSpec options
    ()


printfn "Press any key to exit..."
System.Console.ReadKey ()
|> ignore

