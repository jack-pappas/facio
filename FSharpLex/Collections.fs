(*

Copyright 2010 Oliver Friedmann, Martin Lange
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

namespace FSharpLex.SpecializedCollections

open System
open System.Collections.Generic
open System.CodeDom.Compiler
open System.Diagnostics
open System.Diagnostics.Contracts
open OptimizedClosures
open ExtCore
open ExtCore.Printf
open ExtCore.Collections
open ExtCore.Control


//
type Interval = char * char

//
type CharSet = Interval list

//
type CharSetZipper = ListZipper<Interval>

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module CharSet =
    open LanguagePrimitives
    open OptimizedClosures

    // TEMP : Remove this once we upgrade the 'master' branch of fsharp-tools to ExtCore 0.8.29 or greater.
    /// Classifies the result of a comparison.
    let inline private (|Less|Equal|Greater|) (comparisonResult : int) =
        match comparisonResult with
        | -1 -> Less
        | 0 -> Equal
        | 1 -> Greater
        | invalid ->
            let msg = sprintf "Invalid comparison value. Comparison operations must return -1, 0, or 1. (Value = %i)" invalid
            invalidArg "comparisonResult" msg

    /// Returns the predecessor of the given value.
    let inline private pred (c : char) : char =
        #if CHECKED_ARITHMETIC
        char (Checked.(-) (uint32 c) 1u)
        #else
        char (uint32 c - 1u)
        #endif
    
    /// Returns the successor of the given value.
    let inline private succ (c : char) : char =
        #if CHECKED_ARITHMETIC
        char (Checked.(+) (uint32 c) 1u)
        #else
        char (uint32 c + 1u)
        #endif

    /// Returns the distance between two values -- in other words,
    /// the number of distinct values within the interval defined
    /// by the specified endpoints.
    let inline private dist (lo : char) (hi : char) : int =
        #if CHECKED_ARITHMETIC
        int (Checked.(-) (uint32 hi) (uint32 lo))
        #else
        int (uint32 hi - uint32 lo)
        #endif

    /// The invariant which must be met for an CharSet to be valid.
    let rec (*internal*) invariant (intervals : CharSet) =
        match intervals with
        | [] -> true
        | [(a, b)] ->
            a <= b
        | (a, b) :: ((x, _) :: _ as intervals) ->
            a <= b && (succ b) < x && invariant intervals

    /// The empty CharSet.
    [<CompiledName("Empty")>]
    let empty : CharSet =
        List.Empty

    /// Is the CharSet empty?
    [<CompiledName("IsEmpty")>]
    let isEmpty (intervals : CharSet) =
        List.isEmpty intervals

    /// Creates a new CharSet containing the given value.
    [<CompiledName("Singleton")>]
    let singleton value : CharSet =
        [(value, value)]

    /// Creates a new CharSet containing the given range of values.
    [<CompiledName("OfRange")>]
    let ofRange lo hi : CharSet =
        // Preconditions
        if lo > hi then
            invalidArg "hi" "The upper bound of the interval must be greater than or equal to the lower bound."

        [(lo, hi)]

    /// Does the CharSet contain the given value?
    [<CompiledName("Contains")>]
    let contains value (intervals : CharSet) : bool =
        match intervals with
        | [] ->
            false
        | _ ->
            intervals
            |> List.exists (fun (lo, hi) ->
                lo <= value && value <= hi)

    /// The number of elements in the set.
    [<CompiledName("Count")>]
    let count (set : CharSet) : int =
        (0, set)
        ||> List.fold (fun count (lo, hi) ->
            dist lo hi)

    /// The number of intervals in the set.
    [<CompiledName("IntervalCount")>]
    let intervalCount (set : CharSet) : int =
        List.length set

    //
    [<CompiledName("TryMinElement")>]
    let rec tryMinElement (set : CharSet) : char option =
        match set with
        | [] ->
            None
        | (a, _) :: _ ->
            Some a

    //
    [<CompiledName("TryMaxElement")>]
    let rec tryMaxElement (set : CharSet) : char option =
        match set with
        | [] ->
            None
        | [(_, b)] ->
            Some b
        | _ :: set ->
            tryMinElement set

    //
    [<CompiledName("TryExtractMin")>]
    let rec tryExtractMin (set : CharSet) : char option * CharSet =
        match set with
        | [] ->
            None, set
        | (a, b) :: tl ->
            if a = b then
                Some a, tl
            else
                Some a, ((succ a, b) :: tl)

    //
    [<CompiledName("TryExtractMax")>]
    let rec tryExtractMax (set : CharSet) : char option * CharSet =
        match List.rev set with
        | [] ->
            None, set
        | (a, b) :: tl ->
            let set =
                if a = b then tl
                else (a, pred b) :: tl
            Some b, List.rev set

    /// Returns the lowest (least) value in the set.
    [<CompiledName("MinElement")>]
    let minElement (set : CharSet) : char =
        match tryMinElement set with
        | Some el -> el
        | None ->
            invalidArg "set" "The set is empty."

    /// Returns the highest (greatest) value in the set.
    [<CompiledName("MaxElement")>]
    let maxElement (set : CharSet) : char =
        match tryMaxElement set with
        | Some el -> el
        | None ->
            invalidArg "set" "The set is empty."

    /// Removes the lowest (least) value from the set, returning it along with the updated set.
    [<CompiledName("ExtractMin")>]
    let extractMin (set : CharSet) : char * CharSet =
        let el, set = tryExtractMin set
        match el with
        | Some el ->
            el, set
        | None ->
            invalidArg "set" "The set is empty."

    /// Removes the highest (greatest) value from the set, returning it along with the updated set.
    [<CompiledName("ExtractMax")>]
    let extractMax (set : CharSet) : char * CharSet =
        let el, set = tryExtractMax set
        match el with
        | Some el ->
            el, set
        | None ->
            invalidArg "set" "The set is empty."

    /// Returns a new set with an element added to the set.
    // Returns None if the set was not modified by this operation -- i.e., the set already
    // contained the value; otherwise, returns Some containing the updated set.
    let rec private addImpl (zipper : CharSetZipper) value : CharSet option =
        match ListZipper.context zipper with
        | None, None ->
            Some [(value, value)]
        | Some (a, b), None ->
            // Is the value greater than 'b'?
            if value <= b then
                // Is the value within [a, b]?
                if value >= a then None
                else
                    // Step backwards and retry inserting the value.
                    addImpl (ListZipper.moveBack zipper) value
            else
                // Is the value adjacent to 'b'? In other words, can we just extend [a, b]?
                if succ b = value then
                    zipper
                    |> ListZipper.moveBack
                    |> ListZipper.update (a, value)
                    |> ListZipper.toList
                    |> Some
                else
                    // Insert the value as a single-element interval at the end of the list.
                    zipper
                    |> ListZipper.insert (value, value)
                    |> ListZipper.toList
                    |> Some
        
        | None, Some (a, b) ->
            // Is the value below the lower interval?
            if value < a then
                // Is it "adjacent" to 'a'? I.e., can we merge this value into [a, b]?
                if succ value = a then
                    // Extend [a, b] to include 'value': the result is [value, b].
                    zipper
                    |> ListZipper.update (value, b)
                    |> ListZipper.toList
                    |> Some
                else
                    // Insert the value into the set as a singleton interval.
                    zipper
                    |> ListZipper.insert (value, value)
                    |> ListZipper.toList
                    |> Some
            
            // value >= a
            // Is the value within [a, b]?
            elif value <= b then
                // The value is within [a, b]; return None because
                // the set does not need to be modified.
                None

            else
                // Advance the zipper and retry inserting the value; this allows us
                // to use the context to determine the correct way to insert the value.
                addImpl (ListZipper.moveNext zipper) value

        | Some (a, b), Some (x, y) ->
            // Is the value below the lower interval?
            if value < a then
                // Step backwards so we can use the context to determine how to insert
                // the value (mainly, whether it'll cause two existing intervals to be joined).
                addImpl (ListZipper.moveBack zipper) value

            // value >= a
            // Is the value within [a, b]?
            elif value <= b then
                // The value is within [a, b]; return None because
                // the set does not need to be modified.
                None

            // Is the value "adjacent" to 'b'?
            elif succ b = value then
                // Is the value also "adjacent" to 'x'?
                if succ value = x then
                    // Merge [a, b] with [x, y] at 'value' to get [a, y].
                    zipper
                    |> ListZipper.moveBack
                    |> ListZipper.remove
                    |> ListZipper.update (a, y)
                    |> ListZipper.toList
                    |> Some
                else
                    // Extend [a, b] to include 'value': the result is [a, value].
                    zipper
                    |> ListZipper.moveBack
                    |> ListZipper.update (a, value)
                    |> ListZipper.toList
                    |> Some

            // Is the value less than 'x'?
            elif value < x then
                // Is the value adjacent to 'x'?
                if succ value = x then
                    // Extend [x, y] to include 'value': the result is [value, y].
                    zipper
                    |> ListZipper.update (value, y)
                    |> ListZipper.toList
                    |> Some
                else
                    // Insert the value as a new, singleton interval.
                    zipper
                    |> ListZipper.insert (value, value)
                    |> ListZipper.toList
                    |> Some

            else
                // Advance the zipper and recurse.
                addImpl (ListZipper.moveNext zipper) value

    /// Returns a new set with an element added to the set.
    /// No exception is raised if the set already contains the given element.
    [<CompiledName("Add")>]
    let add value (intervals : CharSet) : CharSet =
        match addImpl (ListZipper.ofList intervals) value with
        | Some res -> res
        | None ->
            // The set wasn't modified, so return the original to
            // preserve structure-sharing within any consuming code.
            intervals

    /// Returns a new set with the given element removed.
    let rec private removeImpl (zipper : CharSetZipper) value : CharSet option =
        match ListZipper.current zipper with
        | None -> None
        | Some (a, b) ->
            if value = a then
                // Handle the special case for a single-element interval.
                if a = b then
                    zipper
                    |> ListZipper.remove
                    |> ListZipper.toList
                    |> Some
                else
                    // Remove 'a' from [a, b]: the result is [a + 1, b].
                    zipper
                    |> ListZipper.update (succ a, b)
                    |> ListZipper.toList
                    |> Some
            elif value = b then
                // Remove 'b' from [a, b]: the result is [a, b - 1].
                zipper
                |> ListZipper.update (a, pred b)
                |> ListZipper.toList
                |> Some
            elif value > a && value < b then
                // The value is in (a, b).
                zipper
                |> ListZipper.remove
                |> ListZipper.insert (succ value, b)
                |> ListZipper.insert (a, pred value)
                |> ListZipper.toList
                |> Some
            else
                // The value doesn't exist in this interval;
                // advance to the next interval and recurse.
                removeImpl (ListZipper.moveNext zipper) value

    /// Returns a new set with the given element removed.
    /// No exception is raised if the set doesn't contain the given element.
    [<CompiledName("Remove")>]
    let remove value (intervals : CharSet) : CharSet =
        // Call the recursive implementation.
        match removeImpl (ListZipper.ofList intervals) value with
        | Some res -> res
        | None ->
            // The set wasn't modified, so return the original to
            // preserve structure-sharing within any consuming code.
            intervals

    /// Computes the union of two sets.
    let rec private unionImpl acc (set1 : CharSet) (set2 : CharSet) : CharSet =
        match set1, set2 with
        | [], [] ->
            // Reverse the list before returning so it's in the correct order.
            List.rev acc

        | [], _ ->
            // Move the non-empty set into the left position to simplify
            // the logic for the next pattern.
            unionImpl acc set2 []

        | hd :: tl, [] ->
            // Add the next interval to the result and recurse.
            unionImpl (hd :: acc) tl []

        | ((a, b) as ab) :: s1, (x, y) :: s2 ->
            // Sort the lists so that 'set1' always has the next-lowest interval.
            // While this incurs a very slight overhead, it greatly simplifies the logic below.
            if x < a then
                unionImpl acc set2 set1
            else
                (*  Now that we know [a, b] is "lower" than [x, y], there are four cases to consider:
                    disjoint, adjacent, partial overlap, complete overlap (subsumption). *)
                let distBetween = dist b x
                if distBetween <= 0 then
                    // The intervals overlap. Determine if it's a partial or complete overlap.
                    if b >= y then
                        // Complete overlap: [x, y] is completely inside [a, b],
                        // so just discard it and recurse.
                        unionImpl acc set1 s2
                    else
                        // Partial overlap. Merge [a, b] and [x, y] into [a, y].
                        // Cons the merged interval back onto 's2' and recurse; it is important that it
                        // be added to 's2' and not 's1', because only then can we be sure that the CharSet
                        // invariant is maintained (i.e., that the merged interval will still be disjoint from,
                        // not adjacent to, and lower than the next interval in the list).
                        unionImpl acc s1 ((a, y) :: s2)
                elif distBetween = 1 then
                    // The intervals are adjacent -- merge them into a single interval.
                    // Cons the merged interval back onto 's2' and recurse; it is important that it
                    // be added to 's2' and not 's1', because only then can we be sure that the CharSet
                    // invariant is maintained (i.e., that the merged interval will still be disjoint from,
                    // not adjacent to, and lower than the next interval in the list).
                    unionImpl acc s1 ((a, y) :: s2)
                else
                    // The intervals are disjoint.
                    // Add the lower interval, [a, b], to the result and recurse.
                    unionImpl (ab :: acc) s1 set2

    /// Computes the union of two sets.
    [<CompiledName("Union")>]
    let union (set1 : CharSet) (set2 : CharSet) : CharSet =
        // Call the recursive implementation.
        unionImpl [] set1 set2

    /// Computes the intersection of two sets.
    let rec private intersectImpl acc (set1 : CharSet) (set2 : CharSet) : CharSet =
        match set1, set2 with
        | [], _
        | _, [] ->
            // Reverse the result before returning, so it'll be ordered correctly.
            List.rev acc

        | (a, b) :: s1, ((x, y) as xy) :: s2 ->
            // Sort the lists so that 'set1' always has the next-lowest interval.
            // While this incurs a very slight overhead, it greatly simplifies the logic below.
            if x < a then
                intersectImpl acc set2 set1
            else
                (*  Now that we know [a, b] is "lower" than [x, y], there are four cases to consider:
                    disjoint, adjacent, partial overlap, complete overlap (subsumption). *)
                let distBetween = dist b x
                if distBetween <= 0 then
                    // The intervals overlap. Determine if it's a partial or complete overlap.
                    if b >= y then
                        // Complete overlap: [x, y] is completely inside [a, b].
                        // The intersection is [x, y] -- add it to the result.
                        // However, the upper part of [a, b] which is not part of the intersection, that is,
                        // [y, b], may intersect with the next interval in 's2', so we add it back to 's1' and recurse.
                        intersectImpl (xy :: acc) ((y, b) :: s1) s2
                    else
                        // Partial overlap. The intersection is [x, b], which is added to the result.
                        // However, the upper part of [x, y] which is not part of the intersection, that is,
                        // [b, y], may intersect with the next interval in 's1', so we add it back to 's2' and recurse.
                        // We know the next interval in 's1' can't have a lower bound less than (b + 2) so
                        // there's no need to worry about the invariant being broken (i.e., because we're not
                        // incrementing the lower bound of the part we're adding back to 's2').
                        intersectImpl ((x, b) :: acc) s1 ((b, y) :: s2)
                else
                    // The intervals are disjoint or adjacent.
                    // Discard the lower interval, [a, b], and recurse.
                    intersectImpl acc s1 set2

    /// Computes the intersection of two sets.
    [<CompiledName("Intersect")>]
    let intersect (set1 : CharSet) (set2 : CharSet) : CharSet =
        // Call the recursive implementation.
        intersectImpl [] set1 set2

    /// Returns a new set with the elements of the second set removed from the first.
    let rec private differenceImpl acc (set1 : CharSet) (set2 : CharSet) : CharSet =
        match set1, set2 with
        | [], _ ->
            // Reverse the result before returning so it's in the correct order.
            List.rev acc

        | hd :: tl, [] ->
            // Add the current element to the result and recurse.
            differenceImpl (hd :: acc) tl []

        | ((a, b) as ab) :: s1, (x, y) :: s2 ->
            match compare a x with
            | Less ->
                match compare b y with
                | Less ->
                    // a < x && b < y
                    match compare b x with
                    | Less ->
                        differenceImpl (ab :: acc) s1 set2
                    | Equal ->
                        differenceImpl ((a, pred b) :: acc) s1 set2
                    | Greater ->
                        differenceImpl ((a, pred x) :: acc) s1 ((b, y) :: s2)
                | Equal ->
                    // Add [a, x - 1] to the result.
                    differenceImpl ((a, pred x) :: acc) s1 s2
                | Greater ->
                    // a < x <= y < b
                    differenceImpl ((a, pred x) :: acc) ((succ y, b) :: s1) s2
            | Equal ->
                match compare b y with
                | Less ->
                    // x = a <= b < y
                    differenceImpl acc s1 set2
                | Equal ->
                    // The intervals are equal.
                    // Discard them both and recurse.
                    differenceImpl acc s1 s2
                | Greater ->
                    // a = x <= y < b
                    differenceImpl acc ((succ y, b) :: s1) s2
            | Greater ->
                match compare b y with
                | Less ->
                    // x < a <= b < y
                    differenceImpl acc s1 ((b, y) :: s2)
                | Equal ->
                    // [x, y] completely contains [a, b].
                    differenceImpl acc s1 s2
                | Greater ->
                    // x < a && y < b
                    match compare a y with
                    | Less ->
                        // x < a < y < b
                        differenceImpl acc ((succ y, b) :: s1) s2
                    | Equal ->
                        differenceImpl acc ((succ a, b) :: s1) s2
                    | Greater ->
                        // x <= y < a <= b
                        differenceImpl acc set1 s2

    /// Returns a new set with the elements of the second set removed from the first.
    [<CompiledName("Difference")>]
    let difference (set1 : CharSet) (set2 : CharSet) : CharSet =
        // Call the recursive implementation.
        differenceImpl [] set1 set2

    //
    let rec private symmDiffImpl acc (set1 : CharSet) (set2 : CharSet) : CharSet =
        match set1, set2 with
        | [], [] ->
            // Reverse the result before returning so it's in the correct order.
            List.rev acc

        | [], _ ->
            // Move the non-empty set into the left position to simplify
            // the logic for the next pattern.
            symmDiffImpl acc set2 []

        | hd :: tl, [] ->
            // Add the next interval to the result and recurse.
            symmDiffImpl (hd :: acc) tl []

        | ((a, b) as ab) :: s1, ((x, y) as xy) :: s2 ->
            // Sort the lists so that 'set1' always has the next-lowest interval.
            // While this incurs a very slight overhead, it greatly simplifies the logic below.
            if x < a then
                symmDiffImpl acc set2 set1
            else
                (*  Now that we know [a, b] is "lower" than [x, y], there are four cases to consider:
                    disjoint, adjacent, partial overlap, complete overlap (subsumption). *)
                let distBetween = dist b x
                if distBetween <= 0 then
                    // The intervals overlap. Determine if it's a partial or complete overlap.
                    if b >= y then
                        // Complete overlap: [x, y] is completely inside [a, b].
                        if x = a then
                            // Nothing to add to the result.
                            if y = b then
                                // The intervals are identical. Discard them both and recurse.
                                symmDiffImpl acc s1 s2
                            else
                                // The remaining range of [a, b] not covered by [x, y],
                                // that is, [y + 1, b] is added back to 's1' so it can be
                                // checked against the next interval in 's2'.
                                symmDiffImpl acc ((succ y, b) :: s1) s2
                        else
                            // There are two parts of [a, b] which aren't covered by [x, y]:
                            // [a, x - 1] and [y + 1, b]. Add the lower range [a, x - 1] to the result;
                            // add the upper range [y + 1, b] back to 's1' so it can be checked
                            // against the next interval in 's2'.
                            symmDiffImpl ((a, pred x) :: acc) ((succ y, b) :: s1) s2
                    else
                        // Partial overlap.
                        if x = a then
                            // Nothing is added to the result here.
                            // The remaining range of [x, y] not covered by [a, b],
                            // that is, [b + 1, y] is added back to 's2' so it can be
                            // checked against the next interval in 's1'.
                            symmDiffImpl acc s1 ((succ b, y) :: s2)
                        else
                            // Add [a, x - 1] to the result.
                            // The remaining range of [x, y] not covered by [a, b],
                            // that is, [b + 1, y] is added back to 's2' so it can be
                            // checked against the next interval in 's1'.
                            symmDiffImpl ((a, pred x) :: acc) s1 ((succ b, y) :: s2)
                elif distBetween = 1 then
                    // The intervals are adjacent -- merge them into a single interval.
                    // Cons the merged interval back onto 's2' and recurse; it is important that it
                    // be added to 's2' and not 's1', because only then can we be sure that the CharSet
                    // invariant is maintained (i.e., that the merged interval will still be disjoint from,
                    // not adjacent to, and lower than the next interval in the list).
                    symmDiffImpl acc s1 ((a, y) :: s2)
                else
                    // The intervals are disjoint.
                    // Add the lower interval, [a, b], to the result and recurse.
                    symmDiffImpl (ab :: acc) s1 set2

    //
    [<CompiledName("SymmetricDifference")>]
    let symmetricDifference (set1 : CharSet) (set2 : CharSet) : CharSet =
        // Call the recursive implementation.
        symmDiffImpl [] set1 set2

    /// Returns a new set with an interval added to the set.
    /// No exception is raised if some or all of the elements in the
    /// given interval are already contained in the set.
    [<CompiledName("AddInterval")>]
    let addInterval (lo, hi) (intervals : CharSet) : CharSet =
        // Preconditions
        if lo > hi then
            argOutOfRange "hi" "The upper bound of the interval cannot be less than the lower bound."

        // TEMP : Implement this operation using 'union'.
        union intervals [(lo, hi)]

    /// Returns a new set with the given interval removed.
    /// No exception is raised if the set does not contain some or all
    /// of the values in the interval.
    [<CompiledName("RemoveInterval")>]
    let removeInterval (lo, hi) (intervals : CharSet) : CharSet =
        // Preconditions
        if lo > hi then
            argOutOfRange "hi" "The upper bound of the interval cannot be less than the lower bound."

        // TEMP : Implement this operation using 'difference'.
        difference intervals [(lo, hi)]

    /// Builds an CharSet from the given enumerable object.
    [<CompiledName("OfSeq")>]
    let ofSeq source : CharSet =
        ([], source)
        ||> Seq.fold (fun intervals el ->
            add el intervals)

    /// Builds an CharSet that contains the same elements as the given list.
    [<CompiledName("OfList")>]
    let ofList source : CharSet =
        ([], source)
        ||> List.fold (fun intervals el ->
            add el intervals)

    /// Builds an CharSet that contains the same elements as the given array.
    [<CompiledName("OfArray")>]
    let ofArray source : CharSet =
        ([], source)
        ||> Array.fold (fun intervals el ->
            add el intervals)

    /// Builds an CharSet that contains the same elements as the given vector.
    [<CompiledName("OfVector")>]
    let ofVector source : CharSet =
        ([], source)
        ||> Vector.fold (fun intervals el ->
            add el intervals)

    /// Builds an CharSet that contains the same elements as the given set.
    [<CompiledName("OfSet")>]
    let ofSet source : CharSet =
        ([], source)
        ||> Set.fold (fun intervals el ->
            add el intervals)

    /// Returns an ordered view of the CharSet as an enumerable object.
    [<CompiledName("ToSeq")>]
    let rec toSeq (set : CharSet) : seq<_> =
        seq {
        match set with
        | [] -> ()
        | (a, b) :: tl ->
            yield! seq { a .. b }
            yield! toSeq tl
        }

    /// Builds a list that contains the elements of the CharSet in order.
    [<CompiledName("ToList")>]
    let toList (set : CharSet) : _ list =
        ([], set)
        ||> List.fold (fun list (lo, hi) ->
            (lo, hi, list)
            |||> Range.fold (fun list el ->
                el :: list))
        |> List.rev

    /// Builds an array that contains the elements of the CharSet in order.
    [<CompiledName("ToArray")>]
    let toArray (set : CharSet) : _[] =
        let elements = ResizeArray (count set)
        set
        |> List.iter (fun (lo, hi) ->
            (lo, hi)
            ||> Range.iter (fun x ->
                elements.Add x))
        ResizeArray.toArray elements

    /// Builds a vector that contains the elements of the CharSet in order.
    [<CompiledName("ToVector")>]
    let toVector (set : CharSet) : vector<_> =
        let elements = ResizeArray (count set)
        set
        |> List.iter (fun (lo, hi) ->
            (lo, hi)
            ||> Range.iter (fun x ->
                elements.Add x))
        
        // OPTIMIZE : Replace this with ResizeArray.toVector from ExtCore 0.8.30.
        ResizeArray.toArray elements
        |> ExtCore.vector.UnsafeCreate

    /// Builds a set that contains the elements of the CharSet in order.
    [<CompiledName("ToSet")>]
    let toSet (set : CharSet) : Set<_> =
        (Set.empty, set)
        ||> List.fold (fun set (lo, hi) ->
            (lo, hi, set)
            |||> Range.fold (fun set el ->
                Set.add el set))

    /// Applies the given function to each element of the set, in order from least to greatest.
    [<CompiledName("Iterate")>]
    let iter (action : char -> unit) (set : CharSet) : unit =
        // Preconditions
        checkNonNull "set" set

        set
        |> List.iter (fun (lo, hi) ->
            Range.iter action lo hi)

    /// Applies the given function to each element of the set, in order from greatest to least.
    [<CompiledName("IterateBack")>]
    let iterBack (action : char -> unit) (set : CharSet) : unit =
        // Preconditions
        checkNonNull "set" set

        set
        |> List.iter (fun (lo, hi) ->
            let lo = int lo
            let hi = int hi
            for x = hi downto lo do
                action (char x))

    /// Applies the given function to each interval of the set, in order from least to greatest.
    [<CompiledName("IterateIntervals")>]
    let iterIntervals (action : char -> char -> unit) (set : CharSet) : unit =
        // Preconditions
        checkNonNull "set" set

        // Return immediately if the set is empty.
        if not <| List.isEmpty set then
            let action = FSharpFunc<_,_,_>.Adapt action

            set
            |> List.iter action.Invoke

    /// <summary>
    /// Tests if any element of the collection satisfies the given predicate.
    /// If the input function is <c>predicate</c> and the elements are <c>i0...iN</c>,
    /// then this function computes predicate <c>i0 or ... or predicate iN</c>.
    /// </summary>
    [<CompiledName("Exists")>]
    let exists (predicate : char -> bool) (set : CharSet) : bool =
        // Preconditions
        checkNonNull "set" set
        
        set
        |> List.exists (fun (lo, hi) ->
            Range.exists predicate lo hi)

    /// <summary>
    /// Tests if all elements of the collection satisfy the given predicate.
    /// If the input function is <c>p</c> and the elements are <c>i0...iN</c>,
    /// then this function computes <c>p i0 && ... && p iN</c>.
    /// </summary>
    [<CompiledName("Forall")>]
    let forall (predicate : char -> bool) (set : CharSet) : bool =
        // Preconditions
        checkNonNull "set" set

        set
        |> List.forall (fun (lo, hi) ->
            Range.forall predicate lo hi)

    /// Applies the given accumulating function to all the elements of the set.
    [<CompiledName("Fold")>]
    let fold (folder : 'State -> char -> 'State) (state : 'State) (set : CharSet) : 'State =
        // Preconditions
        checkNonNull "set" set

        (state, set)
        ||> List.fold (fun state (lo, hi) ->
            let lo = int lo
            let hi = int hi
            let mutable state = state
            for x = lo to hi do
                state <- folder state (char x)
            state)

    /// Applies the given accumulating function to all the elements of the set.
    [<CompiledName("FoldBack")>]
    let foldBack (folder : char -> 'State -> 'State) (set : CharSet) (state : 'State) : 'State =
        // Preconditions
        checkNonNull "set" set

        (set, state)
        ||> List.foldBack (fun (lo, hi) state ->
            let lo = int lo
            let hi = int hi
            let mutable state = state
            for x = hi downto lo do
                state <- folder (char x) state
            state)

    /// Applies the given accumulating function to all the intervals of the set.
    [<CompiledName("FoldIntervals")>]
    let foldIntervals (folder : 'State -> char -> char -> 'State) (state : 'State) (set : CharSet) : 'State =
        // Preconditions
        checkNonNull "set" set

        // Return immediately if the set is empty.
        if List.isEmpty set then state
        else
            let folder = FSharpFunc<_,_,_,_>.Adapt folder

            (state, set)
            ||> List.fold (fun state (lo, hi) ->
                folder.Invoke (state, lo, hi))

    /// Returns a new set containing the results of applying the given function to each element of the input set.
    [<CompiledName("Map")>]
    let map (mapping : char -> char) (set : CharSet) : CharSet =
        // Preconditions
        checkNonNull "set" set

        ([], set)
        ||> List.fold (fun mappedSet (lo, hi) ->
            let lo = int lo
            let hi = int hi
            let mutable mappedSet = mappedSet
            for x = lo to hi do
                mappedSet <- add (mapping (char x)) mappedSet
            mappedSet)

