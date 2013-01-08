(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module internal FSharpLex.Parser

(* NOTE :   The code below is adapted from the 'fslex' grammar, which is
            (c) Microsoft Corporation 2005-2008 and covered under the
            Apache 2.0 license. *)

// turn off warnings that type variables used in production
// annotations are instantiated to concrete type
#nowarn "64"

open Microsoft.FSharp.Text.Lexing
open Microsoft.FSharp.Text.Parsing.ParseHelpers
open FSharpLex.SpecializedCollections
open FSharpLex
open FSharpLex.Ast

// This type is the type of tokens accepted by the parser
type token =
    | EOF
    | BAR
    | DOT
    | PLUS
    | STAR
    | QMARK
    | EQUALS
    | UNDERSCORE
    | LBRACK
    | RBRACK
    | HAT
    | DASH
    | RULE
    | PARSE
    | LET
    | AND
    | LPAREN
    | RPAREN
    | UNICODE_CATEGORY of string
    | CHAR of char
    | CODE of CodeFragment
    | STRING of string
    | IDENT of string

// This type is used to give symbolic names to token indexes, useful for error messages
type tokenId = 
    | TOKEN_EOF
    | TOKEN_BAR
    | TOKEN_DOT
    | TOKEN_PLUS
    | TOKEN_STAR
    | TOKEN_QMARK
    | TOKEN_EQUALS
    | TOKEN_UNDERSCORE
    | TOKEN_LBRACK
    | TOKEN_RBRACK
    | TOKEN_HAT
    | TOKEN_DASH
    | TOKEN_RULE
    | TOKEN_PARSE
    | TOKEN_LET
    | TOKEN_AND
    | TOKEN_LPAREN
    | TOKEN_RPAREN
    | TOKEN_UNICODE_CATEGORY
    | TOKEN_CHAR
    | TOKEN_CODE
    | TOKEN_STRING
    | TOKEN_IDENT
    | TOKEN_end_of_input
    | TOKEN_error

// This type is used to give symbolic names to token indexes, useful for error messages
type nonTerminalId =
    | NONTERM__startspec
    | NONTERM_spec
    | NONTERM_codeopt
    | NONTERM_Macros
    | NONTERM_macro
    | NONTERM_Rules
    | NONTERM_rule
    | NONTERM_args
    | NONTERM_optbar
    | NONTERM_clauses
    | NONTERM_clause
    | NONTERM_regexp
    | NONTERM_charset

/// This function maps integers indexes to symbolic token ids
let private tagOfToken = function
    | EOF -> 0
    | BAR -> 1
    | DOT -> 2
    | PLUS -> 3
    | STAR -> 4
    | QMARK -> 5
    | EQUALS -> 6
    | UNDERSCORE -> 7
    | LBRACK -> 8
    | RBRACK -> 9
    | HAT -> 10
    | DASH -> 11
    | RULE -> 12
    | PARSE -> 13
    | LET -> 14
    | AND -> 15
    | LPAREN -> 16
    | RPAREN -> 17
    | UNICODE_CATEGORY _ -> 18
    | CHAR _ -> 19
    | CODE _ -> 20
    | STRING _ -> 21
    | IDENT _ -> 22

/// This function maps integers indexes to symbolic token ids
let private tokenTagToTokenId = function
    | 0 -> TOKEN_EOF
    | 1 -> TOKEN_BAR
    | 2 -> TOKEN_DOT
    | 3 -> TOKEN_PLUS
    | 4 -> TOKEN_STAR
    | 5 -> TOKEN_QMARK
    | 6 -> TOKEN_EQUALS
    | 7 -> TOKEN_UNDERSCORE
    | 8 -> TOKEN_LBRACK
    | 9 -> TOKEN_RBRACK
    | 10 -> TOKEN_HAT
    | 11 -> TOKEN_DASH
    | 12 -> TOKEN_RULE
    | 13 -> TOKEN_PARSE
    | 14 -> TOKEN_LET
    | 15 -> TOKEN_AND
    | 16 -> TOKEN_LPAREN
    | 17 -> TOKEN_RPAREN
    | 18 -> TOKEN_UNICODE_CATEGORY
    | 19 -> TOKEN_CHAR
    | 20 -> TOKEN_CODE
    | 21 -> TOKEN_STRING
    | 22 -> TOKEN_IDENT
    | 25 -> TOKEN_end_of_input
    | 23 -> TOKEN_error
    | tokenIdx -> failwith "tokenTagToTokenId: bad token"

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
let private prodIdxToNonTerminal = function
    | 0 -> NONTERM__startspec
    | 1 -> NONTERM_spec
    | 2 -> NONTERM_codeopt
    | 3 -> NONTERM_codeopt
    | 4 -> NONTERM_Macros
    | 5 -> NONTERM_Macros
    | 6 -> NONTERM_macro
    | 7 -> NONTERM_Rules
    | 8 -> NONTERM_Rules
    | 9 -> NONTERM_rule
    | 10 -> NONTERM_args
    | 11 -> NONTERM_args
    | 12 -> NONTERM_optbar
    | 13 -> NONTERM_optbar
    | 14 -> NONTERM_clauses
    | 15 -> NONTERM_clauses
    | 16 -> NONTERM_clause
    | 17 -> NONTERM_regexp
    | 18 -> NONTERM_regexp
    | 19 -> NONTERM_regexp
    | 20 -> NONTERM_regexp
    | 21 -> NONTERM_regexp
    | 22 -> NONTERM_regexp
    | 23 -> NONTERM_regexp
    | 24 -> NONTERM_regexp
    | 25 -> NONTERM_regexp
    | 26 -> NONTERM_regexp
    | 27 -> NONTERM_regexp
    | 28 -> NONTERM_regexp
    | 29 -> NONTERM_regexp
    | 30 -> NONTERM_regexp
    | 31 -> NONTERM_charset
    | 32 -> NONTERM_charset
    | 33 -> NONTERM_charset
    | prodIdx -> failwith "prodIdxToNonTerminal: bad production index"

let [<Literal>] private _fsyacc_endOfInputTag = 25
let [<Literal>] private _fsyacc_tagOfErrorTerminal = 23

/// This function gets the name of a token as a string
let private token_to_string = function
    | EOF -> "EOF"
    | BAR -> "BAR"
    | DOT -> "DOT"
    | PLUS -> "PLUS"
    | STAR -> "STAR"
    | QMARK -> "QMARK"
    | EQUALS -> "EQUALS"
    | UNDERSCORE -> "UNDERSCORE"
    | LBRACK -> "LBRACK"
    | RBRACK -> "RBRACK"
    | HAT -> "HAT"
    | DASH -> "DASH"
    | RULE -> "RULE"
    | PARSE -> "PARSE"
    | LET -> "LET"
    | AND -> "AND"
    | LPAREN -> "LPAREN"
    | RPAREN -> "RPAREN"
    | UNICODE_CATEGORY _ -> "UNICODE_CATEGORY"
    | CHAR _ -> "CHAR"
    | CODE _ -> "CODE"
    | STRING _ -> "STRING"
    | IDENT _ -> "IDENT"

// This function gets the data carried by a token as an object
let private _fsyacc_dataOfToken = function
    | EOF -> (null : System.Object)
    | BAR -> (null : System.Object)
    | DOT -> (null : System.Object)
    | PLUS -> (null : System.Object)
    | STAR -> (null : System.Object)
    | QMARK -> (null : System.Object)
    | EQUALS -> (null : System.Object)
    | UNDERSCORE -> (null : System.Object)
    | LBRACK -> (null : System.Object)
    | RBRACK -> (null : System.Object)
    | HAT -> (null : System.Object)
    | DASH -> (null : System.Object)
    | RULE -> (null : System.Object)
    | PARSE -> (null : System.Object)
    | LET -> (null : System.Object)
    | AND -> (null : System.Object)
    | LPAREN -> (null : System.Object)
    | RPAREN -> (null : System.Object)
    | UNICODE_CATEGORY _fsyacc_x -> box _fsyacc_x
    | CHAR _fsyacc_x -> box _fsyacc_x
    | CODE _fsyacc_x -> box _fsyacc_x
    | STRING _fsyacc_x -> box _fsyacc_x
    | IDENT _fsyacc_x -> box _fsyacc_x

let [<Literal>] private _fsyacc_action_rows = 56
let private _fsyacc_gotos = [| 0us; 65535us; 1us; 65535us; 0us; 1us; 2us; 65535us; 0us; 2us; 5us; 6us; 2us; 65535us; 2us; 3us; 8us; 9us; 2us; 65535us; 2us; 8us; 8us; 8us; 2us; 65535us; 4us; 5us; 15us; 16us; 2us; 65535us; 4us; 14us; 15us; 14us; 2us; 65535us; 17us; 18us; 23us; 24us; 1us; 65535us; 20us; 21us; 2us; 65535us; 21us; 22us; 27us; 28us; 2us; 65535us; 21us; 26us; 27us; 26us; 10us; 65535us; 12us; 13us; 13us; 37us; 21us; 29us; 27us; 29us; 29us; 37us; 37us; 37us; 38us; 37us; 39us; 37us; 43us; 38us; 44us; 39us; 5us; 65535us; 46us; 47us; 47us; 55us; 49us; 50us; 50us; 55us; 55us; 55us; |]
let private _fsyacc_sparseGotoTableRowOffsets = [|0us; 1us; 3us; 6us; 9us; 12us; 15us; 18us; 21us; 23us; 26us; 29us; 40us; |]
let private _fsyacc_stateToProdIdxsTableElements = [| 1us; 0us; 1us; 0us; 1us; 1us; 1us; 1us; 1us; 1us; 1us; 1us; 1us; 1us; 1us; 2us; 1us; 5us; 1us; 5us; 1us; 6us; 1us; 6us; 1us; 6us; 6us; 6us; 23us; 24us; 25us; 26us; 27us; 2us; 7us; 8us; 1us; 7us; 1us; 7us; 1us; 9us; 1us; 9us; 1us; 9us; 1us; 9us; 1us; 9us; 1us; 9us; 1us; 11us; 1us; 11us; 1us; 13us; 2us; 14us; 15us; 1us; 14us; 1us; 14us; 6us; 16us; 23us; 24us; 25us; 26us; 27us; 1us; 16us; 1us; 17us; 1us; 18us; 1us; 19us; 1us; 20us; 1us; 21us; 1us; 22us; 6us; 23us; 23us; 24us; 25us; 26us; 27us; 6us; 23us; 24us; 25us; 26us; 27us; 27us; 6us; 23us; 24us; 25us; 26us; 27us; 28us; 1us; 24us; 1us; 25us; 1us; 26us; 1us; 27us; 1us; 28us; 1us; 28us; 2us; 29us; 30us; 2us; 29us; 33us; 1us; 29us; 1us; 30us; 2us; 30us; 33us; 1us; 30us; 2us; 31us; 32us; 1us; 32us; 1us; 32us; 2us; 33us; 33us; |]
let private _fsyacc_stateToProdIdxsTableRowOffsets = [|0us; 2us; 4us; 6us; 8us; 10us; 12us; 14us; 16us; 18us; 20us; 22us; 24us; 26us; 33us; 36us; 38us; 40us; 42us; 44us; 46us; 48us; 50us; 52us; 54us; 56us; 58us; 61us; 63us; 65us; 72us; 74us; 76us; 78us; 80us; 82us; 84us; 86us; 93us; 100us; 107us; 109us; 111us; 113us; 115us; 117us; 119us; 122us; 125us; 127us; 129us; 132us; 134us; 137us; 139us; 141us; |]
let private _fsyacc_actionTableElements = [|1us; 16387us; 20us; 7us; 0us; 49152us; 1us; 16388us; 14us; 10us; 1us; 32768us; 12us; 4us; 1us; 32768us; 22us; 17us; 1us; 16387us; 20us; 7us; 0us; 16385us; 0us; 16386us; 1us; 16388us; 14us; 10us; 0us; 16389us; 1us; 32768us; 22us; 11us; 1us; 32768us; 6us; 12us; 8us; 32768us; 0us; 33us; 7us; 34us; 8us; 46us; 16us; 44us; 18us; 32us; 19us; 31us; 21us; 35us; 22us; 36us; 12us; 16390us; 0us; 33us; 1us; 43us; 3us; 40us; 4us; 41us; 5us; 42us; 7us; 34us; 8us; 46us; 16us; 44us; 18us; 32us; 19us; 31us; 21us; 35us; 22us; 36us; 1us; 16392us; 15us; 15us; 1us; 32768us; 22us; 17us; 0us; 16391us; 1us; 16394us; 22us; 23us; 1us; 32768us; 6us; 19us; 1us; 32768us; 13us; 20us; 1us; 16396us; 1us; 25us; 8us; 32768us; 0us; 33us; 7us; 34us; 8us; 46us; 16us; 44us; 18us; 32us; 19us; 31us; 21us; 35us; 22us; 36us; 0us; 16393us; 1us; 16394us; 22us; 23us; 0us; 16395us; 0us; 16397us; 1us; 16399us; 1us; 27us; 8us; 32768us; 0us; 33us; 7us; 34us; 8us; 46us; 16us; 44us; 18us; 32us; 19us; 31us; 21us; 35us; 22us; 36us; 0us; 16398us; 13us; 32768us; 0us; 33us; 1us; 43us; 3us; 40us; 4us; 41us; 5us; 42us; 7us; 34us; 8us; 46us; 16us; 44us; 18us; 32us; 19us; 31us; 20us; 30us; 21us; 35us; 22us; 36us; 0us; 16400us; 0us; 16401us; 0us; 16402us; 0us; 16403us; 0us; 16404us; 0us; 16405us; 0us; 16406us; 11us; 16407us; 0us; 33us; 3us; 40us; 4us; 41us; 5us; 42us; 7us; 34us; 8us; 46us; 16us; 44us; 18us; 32us; 19us; 31us; 21us; 35us; 22us; 36us; 11us; 16411us; 0us; 33us; 3us; 40us; 4us; 41us; 5us; 42us; 7us; 34us; 8us; 46us; 16us; 44us; 18us; 32us; 19us; 31us; 21us; 35us; 22us; 36us; 13us; 32768us; 0us; 33us; 1us; 43us; 3us; 40us; 4us; 41us; 5us; 42us; 7us; 34us; 8us; 46us; 16us; 44us; 17us; 45us; 18us; 32us; 19us; 31us; 21us; 35us; 22us; 36us; 0us; 16408us; 0us; 16409us; 0us; 16410us; 8us; 32768us; 0us; 33us; 7us; 34us; 8us; 46us; 16us; 44us; 18us; 32us; 19us; 31us; 21us; 35us; 22us; 36us; 8us; 32768us; 0us; 33us; 7us; 34us; 8us; 46us; 16us; 44us; 18us; 32us; 19us; 31us; 21us; 35us; 22us; 36us; 0us; 16412us; 2us; 32768us; 10us; 49us; 19us; 52us; 2us; 32768us; 9us; 48us; 19us; 52us; 0us; 16413us; 1us; 32768us; 19us; 52us; 2us; 32768us; 9us; 51us; 19us; 52us; 0us; 16414us; 1us; 16415us; 11us; 53us; 1us; 32768us; 19us; 54us; 0us; 16416us; 1us; 16417us; 19us; 52us; |]
let private _fsyacc_actionTableRowOffsets = [|0us; 2us; 3us; 5us; 7us; 9us; 11us; 12us; 13us; 15us; 16us; 18us; 20us; 29us; 42us; 44us; 46us; 47us; 49us; 51us; 53us; 55us; 64us; 65us; 67us; 68us; 69us; 71us; 80us; 81us; 95us; 96us; 97us; 98us; 99us; 100us; 101us; 102us; 114us; 126us; 140us; 141us; 142us; 143us; 152us; 161us; 162us; 165us; 168us; 169us; 171us; 174us; 175us; 177us; 179us; 180us; |]
let private _fsyacc_reductionSymbolCounts = [|1us; 5us; 1us; 0us; 0us; 2us; 4us; 3us; 1us; 6us; 0us; 2us; 0us; 1us; 3us; 1us; 2us; 1us; 1us; 1us; 1us; 1us; 1us; 2us; 2us; 2us; 2us; 3us; 3us; 3us; 4us; 1us; 3us; 2us; |]
let private _fsyacc_productionToNonTerminalTable = [|0us; 1us; 2us; 2us; 3us; 3us; 4us; 5us; 5us; 6us; 7us; 7us; 8us; 8us; 9us; 9us; 10us; 11us; 11us; 11us; 11us; 11us; 11us; 11us; 11us; 11us; 11us; 11us; 11us; 11us; 11us; 12us; 12us; 12us; |]
let private _fsyacc_immediateActions = [|65535us; 49152us; 65535us; 65535us; 65535us; 65535us; 16385us; 16386us; 65535us; 16389us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 16391us; 65535us; 65535us; 65535us; 65535us; 65535us; 16393us; 65535us; 16395us; 16397us; 65535us; 65535us; 16398us; 65535us; 16400us; 16401us; 16402us; 16403us; 16404us; 16405us; 16406us; 65535us; 65535us; 65535us; 16408us; 16409us; 16410us; 65535us; 65535us; 16412us; 65535us; 65535us; 16413us; 65535us; 65535us; 16414us; 65535us; 65535us; 16416us; 65535us; |]
let private _fsyacc_reductions = [| 
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : Specification)) in
            box
                (
                   (
                      raise (Microsoft.FSharp.Text.Parsing.Accept(box _1))
                   )
                 : '_startspec));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'codeopt)) in
            let _2 = (let data = parseState.GetInput(2) in (unbox data : 'Macros)) in
            let _4 = (let data = parseState.GetInput(4) in (unbox data : 'Rules)) in
            let _5 = (let data = parseState.GetInput(5) in (unbox data : 'codeopt)) in
            box
                (
                   (
                      // Specification
                      { Header = _1;
                        Footer = _5;
                        Macros = _2;
                        Rules = _4;
                        }
                   )
                 : Specification));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : CodeFragment)) in
            box
                (
                   (
                      Some _1 
                   )
                 : 'codeopt));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            box
                (
                   (
                      None
                   )
                 : 'codeopt));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            box
                (
                   (
                      [] 
                   )
                 : 'Macros));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'macro)) in
            let _2 = (let data = parseState.GetInput(2) in (unbox data : 'Macros)) in
            box
                (
                   (
                      _1 :: _2 
                   )
                 : 'Macros));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (unbox data : MacroIdentifier)) in
            let _4 = (let data = parseState.GetInput(4) in (unbox data : 'regexp)) in
            box
                (
                   (
                      match _4 with
                      | Pattern _4 ->
                        let pos =
                            let rawStartPos, rawEndPos = parseState.ResultRange
                            let startPos = SourcePosition (uint32 rawStartPos.Line, uint32 rawStartPos.Column)
                            let endPos = SourcePosition (uint32 rawEndPos.Line, uint32 rawEndPos.Column)
                            Some (startPos, endPos)
                        ((pos, _2), _4)
                      | EndOfFile ->
                        let msg = sprintf "End-of-file pattern in macro '%s'." _2
                        raise <| exn msg
                   )
                 : 'macro));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'rule)) in
            let _3 = (let data = parseState.GetInput(3) in (unbox data : 'Rules)) in
            box
                (
                   (
                      _1 :: _3 
                   )
                 : 'Rules));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'rule)) in
            box
                (
                   ( 
                      [_1] 
                   )
                 : 'Rules));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : RuleIdentifier)) in
            let _2 = (let data = parseState.GetInput(2) in (unbox data : 'args)) in
            let _5 = (let data = parseState.GetInput(5) in (unbox data : 'optbar)) in
            let _6 = (let data = parseState.GetInput(6) in (unbox data : 'clauses)) in
            box
                (
                   (
                      let rule = {
                          Parameters = _2;
                          Clauses = _6; }
                      let pos =
                            let rawStartPos, rawEndPos = parseState.ResultRange
                            let startPos = SourcePosition (uint32 rawStartPos.Line, uint32 rawStartPos.Column)
                            let endPos = SourcePosition (uint32 rawEndPos.Line, uint32 rawEndPos.Column)
                            Some (startPos, endPos)
                      
                      ((pos, _1), rule)
                   )
                 : 'rule));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            box
                (
                   (
                      [] 
                   )
                 : 'args));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : ParameterName)) in
            let _2 = (let data = parseState.GetInput(2) in (unbox data : 'args)) in
            box
                (
                   (
                      _1 :: _2
                   )
                 : 'args));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            box
                (
                   (
                   )
                 : 'optbar));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            box
                (
                   (
                      
                   )
                 : 'optbar));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'clause)) in
            let _3 = (let data = parseState.GetInput(3) in (unbox data : 'clauses)) in
            box
                (
                   (
                     _1 :: _3
                   )
                 : 'clauses));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'clause)) in
            box
                (
                   (
                      [_1]
                   )
                 : 'clauses));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'regexp)) in
            let _2 = (let data = parseState.GetInput(2) in (unbox data : CodeFragment)) in
            box
                (
                   (
                      { Pattern = _1; Action = _2; }
                   )
                 : 'clause));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : char)) in
            box
                (
                   (
                      Pattern <| Character _1
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : string)) in
            box
                (
                   (
                      //UnicodeCategory _1
                      raise <| System.NotImplementedException "UnicodeCategory pattern"
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            box
                (
                   (
                      EndOfFile
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            box
                (
                   (
                      Pattern Any 
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : string)) in
            box
                (
                   (
                      Pattern <| Pattern.literalString _1
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : string)) in
            box
                (
                   (
                      Pattern <| Macro _1 
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'regexp)) in
            let _2 = (let data = parseState.GetInput(2) in (unbox data : 'regexp)) in
            box
                (
                   (
                      match _1, _2 with
                      | Pattern _1, Pattern _2 ->
                        Pattern <| Concat (_1, _2)
                      | _ ->
                        raise <| exn "End-of-file marker in Concat pattern."
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'regexp)) in
            box
                (
                   (
                      match _1 with
                      | Pattern _1 ->
                         Pattern <| OneOrMore _1
                      | EndOfFile ->
                        raise <| exn "End-of-file marker in OneOrMore pattern."
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'regexp)) in
            box
                (
                   (
                      match _1 with
                      | Pattern _1 ->
                         Pattern <| Star _1
                      | EndOfFile ->
                         raise <| exn "End-of-file marker in Star pattern."
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'regexp)) in
            box
                (
                   (
                      match _1 with
                      | Pattern _1 ->
                        Pattern <| Optional _1
                      | EndOfFile ->
                        raise <| exn "End-of-file marker in Optional pattern."
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'regexp)) in
            let _3 = (let data = parseState.GetInput(3) in (unbox data : 'regexp)) in
            box
                (
                   (
                      match _1, _3 with
                      | Pattern _1, Pattern _3 ->
                        Pattern <| Or (_1, _3)
                      | _ ->
                        raise <| exn "End-of-file marker in Or pattern."
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (unbox data : 'regexp)) in
            box
                (
                   (
                      _2
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (unbox data : 'charset)) in
            box
                (
                   (
                      Pattern <| CharacterSet _2
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _3 = (let data = parseState.GetInput(3) in (unbox data : 'charset)) in
            box
                (
                   (
                      Pattern <| Negate (CharacterSet _3)
                   )
                 : 'regexp));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : char)) in
            box
                (
                   (
                      CharSet.singleton _1
                   )
                 : 'charset));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : char)) in
            let _3 = (let data = parseState.GetInput(3) in (unbox data : char)) in
            box
                (
                   (
                      CharSet.ofRange _1 _3
                   )
                 : 'charset));
        (fun (parseState : Microsoft.FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (unbox data : 'charset)) in
            let _2 = (let data = parseState.GetInput(2) in (unbox data : 'charset)) in
            box
                (
                   (
                      CharSet.union _1 _2
                   )
                 : 'charset));
|]

let private tables : Microsoft.FSharp.Text.Parsing.Tables<_> = {
    reductions = _fsyacc_reductions;
    endOfInputTag = _fsyacc_endOfInputTag;
    tagOfToken = tagOfToken;
    dataOfToken = _fsyacc_dataOfToken;
    actionTableElements = _fsyacc_actionTableElements;
    actionTableRowOffsets = _fsyacc_actionTableRowOffsets;
    stateToProdIdxsTableElements = _fsyacc_stateToProdIdxsTableElements;
    stateToProdIdxsTableRowOffsets = _fsyacc_stateToProdIdxsTableRowOffsets;
    reductionSymbolCounts = _fsyacc_reductionSymbolCounts;
    immediateActions = _fsyacc_immediateActions;
    gotos = _fsyacc_gotos;
    sparseGotoTableRowOffsets = _fsyacc_sparseGotoTableRowOffsets;
    tagOfErrorTerminal = _fsyacc_tagOfErrorTerminal;
    parseError = (fun (ctxt : Microsoft.FSharp.Text.Parsing.ParseErrorContext<_>) ->
                              match parse_error_rich with
                              | Some f -> f ctxt
                              | None -> parse_error ctxt.Message);
    numTerminals = 26;
    productionToNonTerminalTable = _fsyacc_productionToNonTerminalTable; }

let engine lexer lexbuf startState =
    tables.Interpret (lexer, lexbuf, startState)

let spec lexer lexbuf : Specification =
    unbox <| tables.Interpret (lexer, lexbuf, 0)
