(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.Analysis

open Grammar


/// Classifies a parser position (within a parser item), based on
/// how the insertion of a semantic routine at that position would
/// change the classification of the grammar.
type PositionClassification =
    /// No semantic routine may be called at this position.
    // Inserting a semantic routine here always causes the grammar
    // to become non-deterministic.
    | Forbidden
    /// It is sometimes safe to call a semantic routine at this position.
    // Inserting a semantic routine here may cause the grammar to
    // become non-deterministic.
    | Contingent
    /// It is always safe to call a semantic routine at this position.
    // Inserting a semantic routine here preserves the grammar class;
    // e.g., an LR(1) grammar will still be LR(1) after inserting the routine.
    | Free

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Grammar =
    (* TODO :   Implement functions to perform other useful analyses on grammars; for example:
                    - Detect unreachable/dead nonterminals
                    - Detect unreachable productions (i.e., productions overlapped by some earlier
                      production of the same nonterminal).
                    - Ambiguity detection.

                These analyses are probably easiest to implement using a graph representation
                of a grammar, so we'll also need to implement a decent sparse graph library. *)

    //
    let classifyPositions (grammar : Grammar<'NonterminalId, 'Token>) =
        // TODO : Need to implement some graph functionality (for dominators)
        // before this algorithm can be implemented.
        failwith "TODO"

