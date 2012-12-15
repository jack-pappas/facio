(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

namespace FSharpYacc.Analysis

open FSharpYacc.Grammar


//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private PartialStateGraph =
    //
    let create (grammar : Grammar<'Nonterminal, 'Terminal>) =
        raise <| System.NotImplementedException "PartialStateGraph.create"



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

    /// <summary>Classifies the parser positions of the input grammar to determine
    /// where it is safe to insert semantic actions.</summary>
    /// <returns>A Map containing the classifications of the parser positions
    /// in the productions of the input grammar. Note that for a production with
    /// N symbols, there are N+1 positions, so each array in the returned map will
    /// contain one (1) more element than it's corresponding production.</returns>
    /// <remarks>
    /// Reference : "Semantic Routines and LR(k) Parsers" by Purdom and Brown.
    /// </remarks>
    static member Classify (grammar : Grammar<'Nonterminal, 'Terminal>)
        : Map<'Nonterminal, PositionClassification[][]> =
        // TODO : Need to implement some graph functionality (for dominators)
        // before this algorithm can be implemented.
        failwith "TODO"



