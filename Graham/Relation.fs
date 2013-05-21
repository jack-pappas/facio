(*

Copyright 2012-2013 Jack Pappas

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

//
namespace Graham.Graph

open System.Diagnostics

(*  Turn off warning about uppercase variable identifiers;
    some variables in the code below are named using the
    F# backtick syntax so they can use names resembling
    the formulas they implement. *)
#nowarn "49"


/// Partial function.
type internal PartialFunction<'T, 'U
    when 'T : comparison
    and 'U : comparison> =
    Map<'T, Set<'U>>

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal PartialFunction =
    //
    let empty : PartialFunction<'T, 'U> = Map.empty

    //
    let add source target (func : PartialFunction<'T,' U>) : PartialFunction<'T,' U> =
        let targets =
            match Map.tryFind source func with
            | None ->
                Set.singleton target
            | Some targets ->
                Set.add target targets

        Map.add source targets func

/// A binary relation over a set of elements.
// For each 'x', contains the 'y' values such that xRy (given a relation 'R').
type internal Relation<'T when 'T : comparison> =
    Map<'T, Set<'T>>

/// The traversal status of an element.
type private TraversalStatus =
    /// The element has not yet been traversed.
    | NotStarted
    /// Traversal of the element is in-progress.
    | InProgress of int // depth
    /// Traversal of the element has been completed.
    | Completed

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal Relation =
    //
    let empty : Relation<'T> = Map.empty

    //
    let add source target (relation : Relation<'T>) : Relation<'T> =
        let targets =
            match Map.tryFind source relation with
            | None ->
                Set.singleton target
            | Some targets ->
                Set.add target targets

        Map.add source targets relation

    //
    let rec private traverse (x, N, stack, F, X : Set<'T>, R : Relation<'T>, F' : PartialFunction<'T, 'U>)
        : Map<_,_> * Map<_,_> * _ list =
        let stack = x :: stack
        let d = List.length stack
        let N = Map.add x (InProgress d) N
        let F =
            let ``F'(x)`` = Map.find x F'
            Map.add x ``F'(x)`` F

        // Find the 'y' values related to 'x' and compute xRy
        // by recursively traversing them.
        let F, N, stack =
            match Map.tryFind x R with
            | None ->
                F, N, stack
            | Some ``R(x)`` ->
                ((F, N, stack), ``R(x)``)
                ||> Set.fold (fun (F, N, stack) y ->
                    let F, N, stack =
                        match Map.find y N with
                        | NotStarted ->
                            traverse (y, N, stack, F, X, R, F')
                        | _ ->
                            F, N, stack

                    let N =
                        let ``N(x)`` = Map.find x N
                        let ``N(y)`` = Map.find y N
                        Map.add x (min ``N(x)`` ``N(y)``) N

                    let F =
                        match Map.tryFind y F with
                        | None -> F
                        | Some ``F(y)`` ->
                            let ``F(x)`` = Map.find x F
                            Map.add x (Set.union ``F(x)`` ``F(y)``) F

                    F, N, stack)

        // Walk back up the stack, if necessary.
        match Map.find x N with
        | InProgress depth when depth = d ->
            let ``F(x)`` = Map.find x F
            let rec unwind (F, N, stack) =
                match stack with
                | [] ->
                    failwith "Unexpectedly empty stack."
                | element :: stack ->
                    let N = Map.add element Completed N
                    let F = Map.add element ``F(x)`` F

                    if element = x then
                        F, N, stack
                    else
                        unwind (F, N, stack)

            unwind (F, N, stack)

        | _ ->
            F, N, stack

    /// <summary>The 'digraph' algorithm from DeRemer and Pennello's paper.</summary>
    /// <remarks>This algorithm quickly computes set relations by 'condensing'
    /// a relation graph's strongly-connected components (SCCs), then performing
    /// a bottom-up traversal of the resulting DAG.</remarks>
    /// <param name="X">The set on which the relation is defined.</param>
    /// <param name="R">A relation on <paramref name="X"/>.</param>
    /// <param name="F'">A function from <paramref name="X"/> to sets.</param>
    /// <returns><c>F</c>, a function from X to sets, such that <c>F x</c> satisfies
    /// equation 4.1 in DeRemer and Pennello's paper.</returns>
    let digraph (X : Set<'T>, R : Relation<'T>, F' : PartialFunction<'T, 'U>) =
        //
        let N =
            (Map.empty, X)
            ||> Set.fold (fun N x ->
                Map.add x NotStarted N)

        ((Map.empty, N, []), X)
        ||> Set.fold (fun (F, N, stack) x ->
            match Map.find x N with
            | NotStarted ->
                traverse (x, N, stack, F, X, R, F')
            | _ ->
                F, N, stack)
        #if DEBUG
        // DEBUG : Make sure all set elements have been completely traversed.
        |> tap (fun (_, N, _) ->
            let untraversed =
                X |> Set.filter (fun x ->
                    Map.find x N <> Completed)
            Debug.Assert (
                Set.isEmpty untraversed,
                sprintf "There are %i elements of X (Count = %i) which have not been completely traversed." (Set.count untraversed) (Set.count X))
            )
        #endif
        // Discard the intermediate variables
        |> fun (F, _, _) -> F