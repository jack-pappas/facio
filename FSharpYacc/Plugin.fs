(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
namespace FSharpYacc.Plugin

open System.ComponentModel.Composition
open FSharpYacc.Ast
open Graham
open Graham.LR
open FSharpYacc
open FSharpYacc.Compiler

(* TODO :   Determine how the user will select the backend they want to use,
            and also how we can allow backend-specific options to be specified. *)

//
[<Interface>]
type IBackend =
    /// <summary>Invokes this backend to (e.g., emit code) for the compiled parser specification.</summary>
    /// <param name="processedSpec">The processed parser specification.</param>
    /// <param name="taggedGrammar">The tagged grammar which was created from the parser specification and used to create the parser table.</param>
    /// <param name="parserTable">The LR(0)-based (i.e., SLR(1) or LALR(1)) parser table compiled from the parser specification.</param>
    /// <param name="options">Options which control the behavior of the backend.</param>
    abstract Invoke :
        processedSpec : ProcessedSpecification<NonterminalIdentifier, TerminalIdentifier>
        * taggedGrammar : TaggedAugmentedGrammar<NonterminalIdentifier, TerminalIdentifier>
        * parserTable : Lr0ParserTable<NonterminalIdentifier, TerminalIdentifier>
        * options : CompilationOptions
        // TODO : Add parameter for logging interface?
        -> unit
