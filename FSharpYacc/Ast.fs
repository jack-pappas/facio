(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.Ast


/// A symbol within a context-free grammar (CFG).
type Symbol<'NonterminalId, 'Token
                when 'NonterminalId : comparison
                and 'Token : comparison> =
    //
    | Terminal of 'Token
    //
    | Nonterminal of 'NonterminalId

    override this.ToString () =
        match this with
        | Terminal token ->
            token.ToString ()
        | Nonterminal nonterm ->
            nonterm.ToString ()

/// A context-free grammar (CFG).
type Grammar<'NonterminalId, 'Token
                when 'NonterminalId : comparison
                and 'Token : comparison> = {
    //
    Terminals : Set<'Token>;
    //
    Nonterminals : Set<'NonterminalId>;
    //
    Productions : Map<'NonterminalId, Set<Symbol<'NonterminalId, 'Token>[]>>;
    //
    StartSymbol : 'NonterminalId;
}

(* TODO :   Create a new internal record type, GrammarWithSets (or similar) which
            contains the same fields as Grammar, plus the FIRST/FOLLOW/nullable sets. *)
