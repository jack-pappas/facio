(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module internal FSharpLex.TestSpec

open Ast    // TEMP : Remove this once the testing code (below) is removed.


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
        Pattern.Or (
            Pattern.ofCharRange 'A' 'Z',
            Pattern.ofCharRange 'a' 'z')

    let digit =
        // ['0'-'9']
        Pattern.ofCharRange '0' '9'

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
                        Pattern.ofCharList ['\\' ; '\'' ; '"' ; 'n' ; 't' ; 'b' ; 'r'])),
                Character '\''))

    let hex =
        // ['0'-'9'] | ['A'-'F'] | ['a'-'f']
        Pattern.orArray [|
            Pattern.ofCharRange '0' '9';
            Pattern.ofCharRange 'A' 'F';
            Pattern.ofCharRange 'a' 'f';
        |]

    let hexgraph =
        // '\\' 'x' hex hex
        Pattern.concatArray [|
            Character '\\';
            Character 'x';
            Macro "hex";
            Macro "hex";
        |]

    let trigraph =
        // '\\' digit digit digit
        Pattern.concatArray [|
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
        Pattern.orArray [|
            Macro "ident_start_char";
            Macro "digit";
            Pattern.ofCharList ['\''; '_']
            |]

    let ident =
        // ident_start_char ident_char*
        Concat (
            Macro "ident_start_char",
            Star <| Macro "ident_char")

    let unicodegraph_short =
        // '\\' 'u' hex hex hex hex
        Pattern.concatArray [|
            Character '\\';
            Character 'u';
            Macro "hex";
            Macro "hex";
            Macro "hex";
            Macro "hex";
            |]

    let unicodegraph_long =
        // '\\' 'U' hex hex hex hex hex hex hex hex
        Pattern.concatArray [|
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

    [   (None, "letter"), letter;
        (None, "digit"), digit;
        (None, "whitespace"), whitespace;
        (None, "char"), char;
        (None, "hex"), hex;
        (None, "hexgraph"), hexgraph;
        (None, "trigraph"), trigraph;
        (None, "newline"), newline;
        (None, "ident_start_char"), ident_start_char;
        (None, "ident_char"), ident_char;
        (None, "ident"), ident;
        (None, "unicodegraph_short"), unicodegraph_short;
        (None, "unicodegraph_long"), unicodegraph_long; ]
    // Reverse the list before returning, because it's expected to be in reverse order.
    |> List.rev

let ``fslex rules`` =
    [   (None, "token"), {
        Parameters = List.empty;
        Clauses =
            List.rev [
                {   Pattern = Pattern <| Pattern.literalString "rule";
                    Action =
                        "        RULE"; };

                {   Pattern = Pattern <| Pattern.literalString "parse";
                    Action =
                        "        PARSE"; };

                {   Pattern = Pattern <| Pattern.literalString "eof";
                    Action =
                        "        EOF"; };

                {   Pattern = Pattern <| Pattern.literalString "let";
                    Action =
                        "        LET"; };

                {   Pattern = Pattern <| Pattern.literalString "and";
                    Action =
                        "        AND"; };

                {   Pattern = Pattern <| Macro "char";
                    Action =
                        "        let s = lexeme lexbuf\r\n        CHAR (if s.[1] = '\\\\' then escape s.[2] else s.[1])"; };

                {   Pattern =
                        Pattern <|
                        Pattern.concatArray [|
                            Character '\'';
                            Macro "trigraph";
                            Character '\'';
                            |];
                    Action =
                        "        let s = lexeme lexbuf\r\n        CHAR (trigraph s.[2] s.[3] s.[4])"; };

                {   Pattern =
                        Pattern <|
                        Pattern.concatArray [|
                            Character '\'';
                            Macro "hexgraph";
                            Character '\'';
                            |];
                    Action =
                        "        let s = lexeme lexbuf\r\n        CHAR (hexgraph s.[3] s.[4])"; };

                {   Pattern =
                        Pattern <| 
                        Pattern.concatArray [|
                            Character '\'';
                            Macro "unicodegraph_short";
                            Character '\'';
                            |];
                    Action =
                        "        let s = lexeme lexbuf\r\n        CHAR (unicodegraph_short s.[3..6])"; };

                {   Pattern =
                        Pattern <|
                        Pattern.concatArray [|
                            Character '\'';
                            Macro "unicodegraph_long";
                            Character '\'';
                            |];
                    Action =
                        "        let s = lexeme lexbuf\r\n        match unicodegraph_long s.[3..10] with\r\n        | None, c -> CHAR c\r\n        | Some _ , _ -> failwith \"Unicode characters needing surrogate pairs are not yet supported by this tool.\""; };

                {   Pattern =
                        Pattern <|
                        Pattern.concatArray [|
                            Character '\'';
                            Character '\\';
                            Pattern.ofCharRange 'A' 'Z';
                            Pattern.ofCharRange 'a' 'z';
                            Character '\'';                        
                            |];
                    Action =
                        "        let s = (lexeme lexbuf).[2..3]\r\n        UNICODE_CATEGORY s"; };

                {   Pattern = Pattern <| Character '{';
                    Action =
                        "        let p = lexbuf.StartPos\r\n        let buff = StringBuilder 100\r\n        // adjust the first line to get even indentation for all lines w.r.t. the left hand margin\r\n        buff.Append (String.replicate (lexbuf.StartPos.Column + 1) \" \") |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern = Pattern <| Character '"';
                    Action =
                        "        string lexbuf.StartPos (StringBuilder 100) lexbuf"; };

                {   Pattern = Pattern <| OneOrMore (Macro "whitespace");
                    Action =
                        "        token lexbuf"; };

                {   Pattern = Pattern <| Macro "newline";
                    Action =
                        "        newline lexbuf\r\n        token lexbuf"; };

                {   Pattern =
                        Pattern <|
                        Concat (
                            Macro "ident_start_char",
                            Star (Macro "ident_char"));
                    Action =
                        "        IDENT (lexeme lexbuf)"; };

                {   Pattern = Pattern <| Character '|';
                    Action =
                        "        BAR"; };

                {   Pattern = Pattern <| Character '.';
                    Action =
                        "        DOT"; };

                {   Pattern = Pattern <| Character '+';
                    Action =
                        "        PLUS"; };

                {   Pattern = Pattern <| Character '*';
                    Action =
                        "        STAR"; };

                {   Pattern = Pattern <| Character '?';
                    Action =
                        "        QMARK"; };

                {   Pattern = Pattern <| Character '=';
                    Action =
                        "        EQUALS"; };

                {   Pattern = Pattern <| Character '[';
                    Action =
                        "        LBRACK"; };

                {   Pattern = Pattern <| Character ']';
                    Action =
                        "        RBRACK"; };

                {   Pattern = Pattern <| Character '(';
                    Action =
                        "        LPAREN"; };

                {   Pattern = Pattern <| Character ')';
                    Action =
                        "        RPAREN"; };

                {   Pattern = Pattern <| Character '_';
                    Action =
                        "        UNDERSCORE"; };

                {   Pattern = Pattern <| Character '^';
                    Action =
                        "        HAT"; };

                {   Pattern = Pattern <| Character '-';
                    Action =
                        "        DASH"; };

                {   Pattern = Pattern <| Pattern.literalString "(*";
                    Action =
                        "        comment lexbuf.StartPos lexbuf\r\n        |> ignore\r\n        token lexbuf"; };

                {   Pattern =
                        Pattern <|
                        Concat (
                            Pattern.literalString "//",
                            Star (Negate (Pattern.ofCharList ['\n'; '\r'])));
                    Action =
                        "        token lexbuf"; };

                {   Pattern = Pattern Any;
                    Action =
                        "        unexpected_char lexbuf"; };

                {   Pattern = EndOfFile;
                    Action =
                        "        EOF"; };
                ]; };

        (None, "string"), {
        Parameters = ["buff"; "p"];
        Clauses =
            List.rev [
                {   Pattern =
                        Pattern <|
                        Concat (
                            Character '\\',
                            Macro "newline");
                    Action =
                        "        newline lexbuf\r\n        string p buff lexbuf"; };

                {   Pattern =
                        Pattern <|
                        Concat (
                            Character '\\',
                            Pattern.ofCharList ['"' ; '\\' ; '\'' ; 'n' ; 't' ; 'b' ; 'r']);
                    Action =
                        "        buff.Append (escape (lexeme lexbuf).[1]) |> ignore\r\n        string p buff lexbuf"; };

                {   Pattern = Pattern <| Macro "trigraph";
                    Action =
                        "        let s = lexeme lexbuf\r\n        trigraph s.[1] s.[2] s.[3]\r\n        |> buff.Append\r\n        |> ignore\r\n        string p buff lexbuf"; };

                {   Pattern = Pattern <| Character '"';
                    Action =
                        "        STRING <| buff.ToString ()"; };

                {   Pattern = Pattern <| Macro "newline";
                    Action =
                        "        newline lexbuf\r\n        buff.AppendLine () |> ignore\r\n        string p buff lexbuf"; };

                {   Pattern =
                        Pattern <|
                        OneOrMore (
                            Pattern.orArray [|
                                Macro "whitespace";
                                Macro "letter";
                                Macro "digit";
                                |]);
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        string p buff lexbuf"; };

                {   Pattern = EndOfFile;
                    Action =
                        "        let msg = sprintf \"End of file in string started at (%d,%d).\" p.pos_lnum (p.pos_cnum - p.pos_bol)\r\n        raise <| exn msg"; };

                {   Pattern = Pattern Any;
                    Action =
                        "        buff.Append (lexeme lexbuf).[0] |> ignore\r\n        string p buff lexbuf"; };
                ]; };

        (None, "code"), {
        Parameters = ["buff"; "p"];
        Clauses =
            List.rev [
                {   Pattern = Pattern <| Pattern.literalString "}";
                    Action =
                        "        CODE (buff.ToString (), p)"; };

                {   Pattern = Pattern <| Pattern.literalString "{";
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        code p buff lexbuf |> ignore\r\n        buff.Append \"}\" |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern =
                        Pattern <|
                        Concat (
                            Character '\\',
                            Or (Character '"', Character '\\'));
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern = Pattern <| Pattern.literalString "\"";
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        codestring buff lexbuf |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern = Pattern <| Macro "newline";
                    Action =
                        "        newline lexbuf\r\n        buff.AppendLine () |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern =
                        Pattern <|
                        OneOrMore (
                            Pattern.orArray [|
                                Macro "whitespace";
                                Macro "letter";
                                Macro "digit";
                                |]);
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern =
                        Pattern <|
                        Concat (
                            Pattern.literalString "//",
                            Star (Negate (Pattern.ofCharList ['\n'; '\r'])));
                    Action =
                        "        buff.Append (lexeme lexbuf) |> ignore\r\n        code p buff lexbuf"; };

                {   Pattern = EndOfFile;
                    Action =
                        "        EOF"; };

                {   Pattern = Pattern Any;
                    Action =
                        "        buff.Append (lexeme lexbuf).[0] |> ignore\r\n        code p buff lexbuf"; };
                ]; };

        (None, "codestring"), {
        Parameters = ["buff"];
        Clauses =
            List.rev [
                {   Pattern =
                        Pattern <|
                        Concat (
                            Character '\\',
                            Or (Character '"', Character '\\'));
                    Action = "        buff.Append (lexeme lexbuf) |> ignore\r\n        codestring buff lexbuf"; };

                {   Pattern = Pattern <| Character '"';
                    Action = "        buff.Append (lexeme lexbuf) |> ignore\r\n        buff.ToString ()"; };

                {   Pattern = Pattern <| Macro "newline";
                    Action = "        newline lexbuf\r\n        buff.AppendLine () |> ignore\r\n        codestring buff lexbuf"; };

                {   Pattern =
                        Pattern <|
                        OneOrMore (
                            Pattern.orArray [|
                                Macro "whitespace";
                                Macro "letter";
                                Macro "digit";
                                |]);
                    Action = "        buff.Append (lexeme lexbuf) |> ignore\r\n        codestring buff lexbuf"; };

                {   Pattern = EndOfFile;
                    Action = "        failwith \"Unterminated string in code.\""; };

                {   Pattern = Pattern Any;
                    Action = "        buff.Append (lexeme lexbuf).[0] |> ignore\r\n        codestring buff lexbuf"; };
                ]; }

        (None, "comment"), {
        Parameters = ["p"];
        Clauses =
            List.rev [
                {   Pattern = Pattern <| Macro "char";
                    Action = "        comment p lexbuf"; };

                {   Pattern = Pattern <| Character '"';
                    Action = "        try string lexbuf.StartPos (StringBuilder 100) lexbuf\r\n        with Failure s ->\r\n            let msg = s + System.Environment.NewLine + sprintf \"Error while processing string nested in comment started at (%d,%d).\" p.pos_lnum (p.pos_cnum - p.pos_bol)\r\n            raise <| exn msg\r\n        |> ignore\r\n        comment p lexbuf"; };

                {   Pattern = Pattern <| Pattern.literalString "(*";
                    Action = "        try comment p lexbuf\r\n        with Failure s ->\r\n            let msg = s + System.Environment.NewLine + sprintf \"Error while processing nested comment started at (%d,%d).\" p.pos_lnum (p.pos_cnum - p.pos_bol)\r\n            raise <| exn msg\r\n        |> ignore\r\n        comment p lexbuf"; };

                {   Pattern = Pattern <| Macro "newline";
                    Action = "        newline lexbuf\r\n        comment p lexbuf"; };

                {   Pattern = Pattern <| Pattern.literalString "*)";
                    Action = "        ()"; };

                {   Pattern = EndOfFile;
                    Action = "        let msg = sprintf \"End of file in comment started at (%d,%d).\" p.pos_lnum (p.pos_cnum - p.pos_bol)\r\n        raise <| exn msg"; };

                {   Pattern =
                        Pattern <|
                        OneOrMore (
                            Negate (
                                Pattern.ofCharList ['\''; '('; '*'; '\n'; '\r'; '"'; ')']));
                    Action = "        comment p lexbuf"; };

                {   Pattern = Pattern Any;
                    Action = "        comment p lexbuf"; };
                ]; };
        ] // End rule list

let ``fslex specification`` = {
    Header = Some ``fslex header``;
    Footer = None;
    Macros = ``fslex macros``;
    Rules = ``fslex rules``; }

