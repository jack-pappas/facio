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
    [<Test>]
    let find_del_left () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let find_del_right () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let isEmpty () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let contains () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let maxElement () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let minElement () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let bounds () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let comparison () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let equal () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let count () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let intervalCount () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let singleton () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let ofRange () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let add () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let addRange () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let remove () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let union () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let intersect () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let difference () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let fold () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let foldBack () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let iter () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let forall () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let exists () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let toSeq () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let toList () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let toArray () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
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
        [<Test>]
        let dummy () : unit =
            Assert.Ignore "Test not yet implemented."


/// Tests for CharSet.
module CharSet =
    [<Test>]
    let isEmpty () : unit =
        // Check with an empty set.
        CharSet.empty
        |> CharSet.isEmpty
        |> assertTrue

        // Check with a non-empty set.
        CharSet.empty
        |> CharSet.add 'a'
        |> CharSet.isEmpty
        |> assertFalse

    [<Test>]
    let count () : unit =
        // Test case for an empty set.
        CharSet.empty
        |> CharSet.count
        |> assertEqual 0

        // Sample usage test cases.
        CharSet.empty
        |> CharSet.add 'a'
        |> CharSet.add 'b'
        |> CharSet.count
        |> assertEqual 2

        CharSet.ofRange 'A' 'Z'
        |> CharSet.count
        |> assertEqual 26

    [<Test>]
    let intervalCount () : unit =
        // Test case for an empty set.
        CharSet.empty
        |> CharSet.intervalCount
        |> assertEqual 0

        // Sample usage test cases.
        CharSet.ofRange 'A' 'Z'
        |> CharSet.intervalCount
        |> assertEqual 1

        CharSet.empty
        |> CharSet.add 'a'
        |> CharSet.add 'c'
        |> CharSet.add 'e'
        |> CharSet.intervalCount
        |> assertEqual 3

    [<Test>]
    let maxElement () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let minElement () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let singleton () : unit =
        // Sample usage test cases.
        CharSet.singleton 'a'
        |> CharSet.toArray
        |> Collection.assertEqual [| 'a' |]

    [<Test>]
    let contains () : unit =
        // Test case for an empty set.
        CharSet.empty
        |> CharSet.contains '0'
        |> assertFalse

        // Sample usage test cases.
        CharSet.singleton 'b'
        |> CharSet.contains 'a'
        |> assertFalse

        CharSet.singleton 'b'
        |> CharSet.contains 'b'
        |> assertTrue

        CharSet.ofRange 'A' 'E'
        |> CharSet.add 'a'
        |> CharSet.contains 'b'
        |> assertFalse

        CharSet.ofRange 'A' 'E'
        |> CharSet.add 'a'
        |> CharSet.contains 'C'
        |> assertTrue

    [<Test>]
    let add () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let addRange () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let remove () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let exists () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let forall () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let iter () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let iterIntervals () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let fold () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let foldBack () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let map () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let filter () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let ofRange () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let ofSeq () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let ofList () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let ofArray () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let ofSet () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let toSeq () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let toList () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let toArray () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let toSet () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let difference () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let intersect () : unit =
        Assert.Ignore "Test not yet implemented."

    [<Test>]
    let union () : unit =
        Assert.Ignore "Test not yet implemented."


    /// Randomized tests to check for operational equivalence with the standard F# Set type.
    module Randomized =
        /// FsCheck generators for CharSet.
        type CharSetGenerator =
            /// Generates an arbitrary CharSet instance.
            static member CharSet () : Arbitrary<CharSet> =
                gen {
                let! chars = Arb.generate
                return CharSet.ofSeq chars
                } |> Arb.fromGen

        /// Registers the FsCheck generators so they're already loaded
        /// when NUnit runs the tests in this fixture.
        [<TestFixtureSetUp>]
        let registerFsCheckGenerators =
            Arb.register<CharSetGenerator> () |> ignore


        [<Test>]
        let count () : unit =
            assertProp "Equivalence with Set: 'count'" <| fun chars ->
                // Fold over the sequence of chars to create both sets in a single pass.
                let setOfChars, charSet =
                    ((Set.empty, CharSet.empty), chars)
                    ||> Set.fold (fun (setOfChars, charSet) c ->
                        Set.add c setOfChars,
                        CharSet.add c charSet)

                // Do both sets have the same count?
                Set.count setOfChars = CharSet.count charSet

        [<Test>]
        let maxElement () : unit =
            assertProp "Equivalence with Set: 'maxElement'" <| fun chars ->
                // Only test non-empty sequences.
                not (Seq.isEmpty chars) ==> lazy (
                    // Fold over the sequence of chars to create both sets in a single pass.
                    let setOfChars, charSet =
                        ((Set.empty, CharSet.empty), chars)
                        ||> Set.fold (fun (setOfChars, charSet) c ->
                            Set.add c setOfChars,
                            CharSet.add c charSet)

                    // Do the maximum elements of both sets match?
                    Set.maxElement setOfChars = CharSet.maxElement charSet)

        [<Test>]
        let minElement () : unit =
            assertProp "Equivalence with Set: 'minElement'" <| fun chars ->
                // Only test non-empty sequences.
                not (Seq.isEmpty chars) ==> lazy (
                    // Fold over the sequence of chars to create both sets in a single pass.
                    let setOfChars, charSet =
                        ((Set.empty, CharSet.empty), chars)
                        ||> Set.fold (fun (setOfChars, charSet) c ->
                            Set.add c setOfChars,
                            CharSet.add c charSet)

                    // Do the minimum elements of both sets match?
                    Set.minElement setOfChars = CharSet.minElement charSet)

        [<Test>]
        let contains () : unit =
            assertProp "Equivalence with Set: 'contains'" <| fun chars c ->
                // Fold over the sequence of chars to create both sets in a single pass.
                let setOfChars, charSet =
                    ((Set.empty, CharSet.empty), chars)
                    ||> Set.fold (fun (setOfChars, charSet) c ->
                        Set.add c setOfChars,
                        CharSet.add c charSet)

                // Both or neither of the sets should contain 'c'.
                Set.contains c setOfChars = CharSet.contains c charSet

        [<Test>]
        let add () : unit =
            assertProp "Equivalence with Set: 'add'" <| fun setOfChars c ->
                // Create a CharSet from the Set<char>.
                let charSet = CharSet.ofSet setOfChars

                // Add 'c' to both sets.
                let setOfChars = Set.add c setOfChars
                let charSet = CharSet.add c charSet

                // The sets should contain the same elements in the same order.
                (setOfChars, CharSet.toSeq charSet)
                ||> Seq.compareWith compare = 0

        [<Test>]
        let remove () : unit =
            assertProp "Equivalence with Set: 'remove'" <| fun setOfChars c ->
                // Create a CharSet from the Set<char>.
                let charSet = CharSet.ofSet setOfChars

                // Add 'c' to both sets.
                let setOfChars = Set.remove c setOfChars
                let charSet = CharSet.remove c charSet

                // The sets should contain the same elements in the same order.
                (setOfChars, CharSet.toSeq charSet)
                ||> Seq.compareWith compare = 0

        [<Test>]
        let difference () : unit =
            assertProp "Equivalence with Set: 'difference'" <| fun seq1 seq2 ->
                // Create a Set<char> and a CharSet from the first sequence.
                let setOfChars1, charSet1 =
                    ((Set.empty, CharSet.empty), seq1)
                    ||> Set.fold (fun (setOfChars, charSet) c ->
                        Set.add c setOfChars,
                        CharSet.add c charSet)

                // Create a Set<char> and a CharSet from the second sequence.
                let setOfChars2, charSet2 =
                    ((Set.empty, CharSet.empty), seq2)
                    ||> Set.fold (fun (setOfChars, charSet) c ->
                        Set.add c setOfChars,
                        CharSet.add c charSet)

                // Remove the elements of the second sets from the first sets.
                let setOfChars = Set.difference setOfChars1 setOfChars2
                let charSet = CharSet.difference charSet1 charSet2

                // The sets should contain the same elements in the same order.
                (setOfChars, CharSet.toSeq charSet)
                ||> Seq.compareWith compare = 0

        [<Test>]
        let intersect () : unit =
            assertProp "Equivalence with Set: 'intersect'" <| fun seq1 seq2 ->
                // Create a Set<char> and a CharSet from the first sequence.
                let setOfChars1, charSet1 =
                    ((Set.empty, CharSet.empty), seq1)
                    ||> Set.fold (fun (setOfChars, charSet) c ->
                        Set.add c setOfChars,
                        CharSet.add c charSet)

                // Create a Set<char> and a CharSet from the second sequence.
                let setOfChars2, charSet2 =
                    ((Set.empty, CharSet.empty), seq2)
                    ||> Set.fold (fun (setOfChars, charSet) c ->
                        Set.add c setOfChars,
                        CharSet.add c charSet)

                // Intersect the first and second sets.
                let setOfChars = Set.intersect setOfChars1 setOfChars2
                let charSet = CharSet.intersect charSet1 charSet2

                // The sets should contain the same elements in the same order.
                (setOfChars, CharSet.toSeq charSet)
                ||> Seq.compareWith compare = 0

        [<Test>]
        let union () : unit =
            assertProp "Equivalence with Set: 'union'" <| fun seq1 seq2 ->
                // Create a Set<char> and a CharSet from the first sequence.
                let setOfChars1, charSet1 =
                    ((Set.empty, CharSet.empty), seq1)
                    ||> Set.fold (fun (setOfChars, charSet) c ->
                        Set.add c setOfChars,
                        CharSet.add c charSet)

                // Create a Set<char> and a CharSet from the second sequence.
                let setOfChars2, charSet2 =
                    ((Set.empty, CharSet.empty), seq2)
                    ||> Set.fold (fun (setOfChars, charSet) c ->
                        Set.add c setOfChars,
                        CharSet.add c charSet)

                // Union the first and second sets.
                let setOfChars = Set.intersect setOfChars1 setOfChars2
                let charSet = CharSet.intersect charSet1 charSet2

                // The sets should contain the same elements in the same order.
                (setOfChars, CharSet.toSeq charSet)
                ||> Seq.compareWith compare = 0
