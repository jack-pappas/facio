(*

Copyright 2013-2014 Jack Pappas

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

namespace Tests.FSharpLex.SpecializedCollections

open FSharpLex.SpecializedCollections
open NUnit.Framework
open FsUnit
open FsCheck


/// Tests for the balanced DIET (Discrete Interval Encoding Tree).
module CharDiet =
    [<TestCase>]
    let find_del_left () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let find_del_right () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let isEmpty () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let contains () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let maxElement () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let minElement () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let bounds () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let comparison () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let equal () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let count () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let intervalCount () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let singleton () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let ofRange () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let add () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let addRange () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let remove () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let union () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let intersect () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let difference () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let fold () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let foldBack () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let iter () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let forall () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let exists () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let toSeq () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let toList () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let toArray () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let toSet () : unit =
        Assert.Ignore "Test not yet implemented."

    /// Randomized tests to check for operational equivalence with the standard F# Set type.
    module Randomized =
        (*
        /// Determines if the intervals in a DIET are disjoint.
        let rec intervalsDisjointImpl (tree : CharDiet) (elements : Set<char>) =
            match tree with
            | Empty ->
                true, elements
            | Node (l, r, (a, b), _) ->
                match intervalsDisjointImpl l elements with
                | false, elements ->
                    tprintfn "DIET invariant failed: the intervals in the DIET are not disjoint."
                    false, elements
                | true, elements ->
                    // Check that this interval (a, b) is disjoint from the other elements seen so far.
                    let disjoint = Set.isEmpty elements || (Set.maxElement elements < safePred a)

                    // Make sure none of the values in this interval have been seen already.
                    let disjointSet = not <| Range.exists (fun x -> Set.contains x elements) a b

                    if not disjoint || not disjointSet then
                        tprintfn "DIET invariant failed: the intervals in the DIET are not disjoint."
                        false, elements
                    else
                        // Add the elements from this interval to the set.
                        (a, b, elements)
                        |||> Range.fold (fun elements x ->
                            Set.add x elements)
                        // Check the right subtree.
                        |> intervalsDisjointImpl r

        /// Determines if the intervals in a DIET are disjoint.
        let intervalsDisjoint (tree : CharDiet) : bool =
            fst <| intervalsDisjointImpl tree Set.empty
        
        /// Determines if a DIET is correctly formed.
        let rec dietInvariant (tree : CharDiet) =
            match tree with
            | Empty -> true
            | Node (l, r, (a, b), h) ->
                // Check the standard AVL invariant first.
                let height_l = computeHeight l
                let height_r = computeHeight r
                let height_diff = (max height_l height_r) - (min height_l height_r)

                // Is the node balanced (within the allowed tolerance)?
                if height_diff > balanceTolerance then
                    tprintfn "DIET invariant failed: the height difference between the subtrees is invalid."
                    tprintfn "    Height Difference: %i" height_diff
                    tprintfn "    Balance Tolerance: %u" balanceTolerance
                    false

                // Is the height stored in this node correct?
                elif h <> ((max height_l height_r) + 1u) then
                    tprintfn "DIET invariant failed: the height of the node is not set to the correct value."
                    tprintfn "    Node Height: %u (Expected = %u)" h ((max height_l height_r) + 1u)
                    tprintfn "    Left Subtree Height:  %u" height_l
                    tprintfn "    Right Subtree Height: %u" height_r
                    false

                // Check that the interval is correctly directed.
                elif a > b then
                    tprintfn "DIET invariant failed: the DIET contains an incorrectly-directed interval (0x%04x, 0x%04x)." (uint32 a) (uint32 b)
                    false
                else
                // Check the subtrees.
                dietInvariant l
                && dietInvariant r
                // Check that the intervals are disjoint.
                //&& (intervalsDisjoint tree Set.empty |> fst)
    *)
        [<TestCase>]
        let dummy () : unit =
            Assert.Ignore "Test not yet implemented."


/// Tests for CharSet.
module CharSet =
    [<TestCase>]
    let ofSeq () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let ofList () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let ofArray () : unit =
        Assert.Ignore "Test not yet implemented."

    [<TestCase>]
    let ofSet () : unit =
        Assert.Ignore "Test not yet implemented."


    /// Randomized tests to check for operational equivalence with the standard F# Set type.
    module Randomized =
        //
        [<TestCase>]
        let ofSeq () : unit =
            Assert.Ignore "Test not yet implemented."

