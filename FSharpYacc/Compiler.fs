(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.Compiler

open Graham.Grammar
open FSharpYacc.Ast


//
let compile (spec : Specification, options : CompilationOptions) : Choice<_,_> =
    (* TODO :   Validate the specification *)
    //

    (* TODO :   Create the precedence table / comparer from the specification. *)
    //

    (* TODO :   Create a Graham.Grammar from the specification. *)
    //

    (* TODO :   Create the LR(0) automaton from the grammar; report the number of states and
                the number of S/R and R/R conflicts. If there are any conflicts, apply the
                precedence table to the constructed parser table to (possibly) resolve some
                of them. At this point, if there aren't any remaining conflicts, report that
                the grammar is LR(0) and return. *)
    //

    (* TODO :   Upgrade the LR(0) automaton to SLR(1); report the remaining number of S/R and
                R/R conflicts. If there aren't any remaining conflicts, report that the grammar
                is SLR(1) and return. *)
    //

    (* TODO :   Upgrade the LR(0)/SLR(1) automaton to LALR(1); report the remaining number of
                S/R and R/R conflicts. If there aren't any remaining conflicts, report that the
                grammar is LALR(1) and return. *)
    //

    (* TODO :   If we reach this point, the grammar is not LALR(1), but we can still create a
                parser by taking certain actions to resolve any remaining conflicts.
                Emit a _warning_ message for each of these conflicts, specifying the action
                we've taken to resolve it. *)
    //

    
    Choice2Of2 ["Not Implemented: Compiler.compile"]
