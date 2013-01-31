(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpLex.SpecializedCollections

open System.Diagnostics
open OptimizedClosures


(*  NOTE :  The core functions implementing the AVL tree algorithm were extracted into OCaml
            from the "AVL Trees" theory in the Archive of Formal Proofs:
                http://afp.sourceforge.net/entries/AVL-Trees.shtml
            using Isabelle/HOL 2012. The extracted code was adapted to F# (e.g., by adjusting
            the formatting, fixing incomplete pattern-matches), then the supporting functions
            (e.g., 'fold', 'iter') were implemented. *)

/// AVL Tree.
[<NoEquality; NoComparison>]
[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
type private AvlTree<'T when 'T : comparison> =
    /// Empty tree.
    | Empty
    /// Node.
    // Value, Left-Child, Right-Child, Height
    | Node of 'T * AvlTree<'T> * AvlTree<'T> * uint32

/// Functional operators on AVL trees.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private AvlTree =
    open System.Collections.Generic
    open OptimizedClosures

    /// An empty AVL tree.
    let empty : AvlTree<'T> = AvlTree.Empty

    /// Returns the height of an AVL tree's root node.
    let inline height (tree : AvlTree<'T>) =
        match tree with
        | Empty -> 0u
        | Node (_,_,_,h) -> h

    /// Creates an AVL tree whose root node holds the specified value
    /// and the specified left and right subtrees.
    let inline internal create value l (r : AvlTree<'T>) =
        Node (value, l, r, (max (height l) (height r)) + 1u)

    let rec private mkt_bal_l n l (r : AvlTree<'T>) =
        if height l = height r + 2u then
            match l with
            | Empty ->
                failwith "mkt_bal_l"
            | Node (ln, ll, lr, _) ->
                if height ll < height lr then
                    match lr with
                    | Empty ->
                        failwith "mkt_bal_l"
                    | Node (lrn, lrl, lrr, _) ->
                        create lrn (create ln ll lrl) (create n lrr r)
                else
                    create ln ll (create n lr r)
        else
            create n l r

    let rec private mkt_bal_r n l (r : AvlTree<'T>) =
        if height r = height l + 2u then
            match r with
            | Empty ->
                failwith "mkt_bal_r"
            | Node (rn, rl, rr, _) ->
                if height rr < height rl then
                    match rl with
                    | Empty ->
                        failwith "mkt_bal_r"
                    | Node (rln, rll, rlr, _) ->
                        create rln (create n l rll) (create rn rlr rr)
                else
                    create rn (create n l rl) rr
        else
            create n l r

    let rec private delete_max = function
        | Empty ->
            invalidArg "tree" "Cannot delete the maximum value from an empty tree."
        | Node (n, l, Empty, _) ->
            n, l
        | Node (n, l, (Node (_,_,_,_) as right), _) ->
            let na, r = delete_max right
            na, mkt_bal_l n l r

    let private delete_root = function
        | Empty ->
            invalidArg "tree" "Cannot delete the root of an empty tree."
        | Node (_, Empty, r, _) -> r
        | Node (_, (Node (_,_,_,_) as left), Empty, _) ->
            left
        | Node (_, (Node (_,_,_,_) as left), (Node (_,_,_,_) as right), _) ->
            let new_n, l = delete_max left
            mkt_bal_r new_n l right

    /// Creates an AVL tree containing the specified value.
    let singleton value : AvlTree<'T> =
        create value Empty Empty

    /// Determines if an AVL tree is empty.
    let isEmpty (tree : AvlTree<'T>) =
        match tree with
        | Empty -> true
        | Node (_,_,_,_) -> false

    /// Implementation. Returns the height of an AVL tree.
    let rec private computeHeightRec (tree : AvlTree<'T>) cont =
        match tree with
        | Empty ->
            cont 0u
        | Node (_, l, r, _) ->
            computeHeightRec l <| fun height_l ->
            computeHeightRec r <| fun height_r ->
                (max height_l height_r) + 1u
                |> cont

    /// Returns the height of an AVL tree.
    let internal computeHeight (tree : AvlTree<'T>) =
        computeHeightRec tree id
        
    /// Determines if an AVL tree is correctly formed.
    /// It isn't necessary to call this at run-time, though it may be useful for asserting
    /// the correctness of functions which weren't extracted from the Isabelle theory.
    let rec internal avl = function
        | Empty -> true
        | Node (x, l, r, h) ->
            let height_l = computeHeight l
            let height_r = computeHeight r
            height_l = height_r
            || (height_l = (1u + height_r) || height_r = (1u + height_l))
            && h = ((max height_l height_r) + 1u)
            && avl l
            && avl r

    /// Determines if an AVL tree contains a specified value.
    let rec contains (comparer : IComparer<_>) value (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            false
        | Node (n, l, r, _) ->
            let comparison = comparer.Compare (value, n)
            if comparison = 0 then      // value = n
                true
            elif comparison < 0 then    // value < n
                contains comparer value l
            else                        // value > n
                contains comparer value r

    /// Removes the specified value from the tree.
    /// If the tree doesn't contain the value, no exception is thrown;
    /// the tree will be returned without modification.
    let rec delete (comparer : IComparer<_>) x (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            Empty
        | Node (n, l, r, _) as tree ->
            let comparison = comparer.Compare (x, n)
            if comparison = 0 then      // x = n
                delete_root tree
            elif comparison < 0 then    // x < n
                let la = delete comparer x l
                mkt_bal_r n la r
            else                        // x > n
                let a = delete comparer x r
                mkt_bal_l n l a

    /// Adds a value to an AVL tree.
    /// If the tree already contains the value, no exception is thrown;
    /// the tree will be returned without modification.
    let rec insert (comparer : IComparer<_>) x (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            Node (x, Empty, Empty, 1u)
        | Node (n, l, r, _) as tree ->
            let comparison = comparer.Compare (x, n)
            if comparison = 0 then      // x = n
                tree
            elif comparison < 0 then    // x < n
                mkt_bal_l n (insert comparer x l) r
            else                        // x > n
                mkt_bal_r n l (insert comparer x r)

    /// Gets the maximum (greatest) value stored in the AVL tree.
    let rec maxElement (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (n, _, Empty, _) ->
            n
        | Node (_, _, (Node (_,_,_,_) as right), _) ->
            maxElement right

    /// Gets the minimum (least) value stored in the AVL tree.
    let rec minElement (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (n, Empty, _, _) ->
            n
        | Node (_, (Node (_,_,_,_) as left), _, _) ->
            minElement left

    /// Implementation.
    /// Applies the given accumulating function to all elements in an AVL tree.
    let rec private foldRec (folder : FSharpFunc<'State, _, 'State>) (state : 'State) (tree : AvlTree<'T>) cont =
        match tree with
        | Empty ->
            cont state
        | Node (n, l, r, _) ->
            // Fold over the left subtree first.
            foldRec folder state l <| fun state ->
                // Apply the folder function to this node's value.
                let state = folder.Invoke (state, n)

                // Fold over the right subtree.
                foldRec folder state r cont

    /// Applies the given accumulating function to all elements in an AVL tree.
    let fold (folder : 'State -> _ -> 'State) (state : 'State) (tree : AvlTree<'T>) =
        // Call the recursive, CPS-based implementation.
        let folder = FSharpFunc<_,_,_>.Adapt folder
        foldRec folder state tree id

    /// Implementation.
    /// Applies the given accumulating function to all elements in an AVL tree.
    let rec private foldBackRec (folder : FSharpFunc<_, 'State, 'State>) (tree : AvlTree<'T>) (state : 'State) cont =
        match tree with
        | Empty ->
            cont state
        | Node (n, l, r, _) ->
            // Fold over the right subtree first.
            foldBackRec folder r state <| fun state ->
                // Apply the folder function to this node's value.
                let state = folder.Invoke (n, state)

                // Fold backwards over the left subtree.
                foldBackRec folder l state cont

    /// Applies the given accumulating function to all elements in an AVL tree.
    let foldBack (folder : _ -> 'State -> 'State) (tree : AvlTree<'T>) (state : 'State) =
        // Call the recursive, CPS-based implementation.
        let folder = FSharpFunc<_,_,_>.Adapt folder
        foldBackRec folder tree state id

    /// Implementation.
    /// Applies the given accumulating function to all elements in an AVL tree.
    let rec private iterRec (action : _ -> unit) (tree : AvlTree<'T>) cont =
        match tree with
        | Empty ->
            cont ()
        | Node (n, l, r, _) ->
            // Iterate over the left subtree first.
            iterRec action l <| fun () ->
                // Apply the action to this node's value.
                action n

                // Iterate over the right subtree.
                iterRec action r cont

    /// Applies the given function to each element stored in
    /// an AVL tree, in order from least to greatest.
    let iter (action : _ -> unit) (tree : AvlTree<'T>) =
        iterRec action tree id

    /// Counts the number of elements in the tree.
    let count (tree : AvlTree<'T>) =
        (0, tree)
        ||> fold (fun count _ ->
            count + 1)

    /// Extracts the minimum (least) value from an AVL tree,
    /// returning the value along with the updated tree.
    let rec extractMin (comparer : IComparer<_>) (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (n, Empty, r, _) ->
            n, r
        | Node (x, Node (a, left, mid, _), r, _) ->
            // Rebalance the tree at the same time we're traversing downwards
            // to find the minimum value. This avoids the need to perform a
            // second traversal to remove the element once it's found.
            let n = create x mid r
            create a left n
            |> extractMin comparer

    /// Extracts the minimum (least) value from an AVL tree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    let tryExtractMin (comparer : IComparer<_>) (tree : AvlTree<'T>) =
        // Is the tree empty?
        if isEmpty tree then
            None, tree
        else
            let minElement, tree = extractMin comparer tree
            Some minElement, tree

    /// Extracts the maximum (greatest) value from an AVL tree,
    /// returning the value along with the updated tree.
    let rec extractMax (comparer : IComparer<_>) (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (n, l, Empty, _) ->
            n, l
        | Node (x, l, Node (a, mid, right, _), _) ->
            // Rebalance the tree at the same time we're traversing downwards
            // to find the maximum value. This avoids the need to perform a
            // second traversal to remove the element once it's found.
            let n = create x l mid
            create a n right
            |> extractMax comparer

    /// Extracts the maximum (greatest) value from an AVL tree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    let tryExtractMax (comparer : IComparer<_>) (tree : AvlTree<'T>) =
        // Is the tree empty?
        if isEmpty tree then
            None, tree
        else
            let maxElement, tree = extractMax comparer tree
            Some maxElement, tree

    /// Merges two AVL trees and returns the result.
    let union (comparer : IComparer<_>) (tree1 : AvlTree<'T>) (tree2 : AvlTree<'T>) =
        let tree1_count = count tree1
        let tree2_count = count tree2

        // Merge the smaller set into the larger set.
        if tree1_count < tree2_count then
            (tree2, tree1)
            ||> fold (fun tree el ->
                insert comparer el tree)
        else
            (tree1, tree2)
            ||> fold (fun tree el ->
                insert comparer el tree)

    /// Builds a new AVL tree from the elements of a sequence.
    let ofSeq (comparer : IComparer<_>) (sequence : seq<_>) : AvlTree<'T> =
        (Empty, sequence)
        ||> Seq.fold (fun tree el ->
            insert comparer el tree)

    /// Builds a new AVL tree from the elements of an F# list.
    let ofList (comparer : IComparer<_>) (list : _ list) : AvlTree<'T> =
        (Empty, list)
        ||> List.fold (fun tree el ->
            insert comparer el tree)

    /// Builds a new AVL tree from the elements of an array.
    let ofArray (comparer : IComparer<_>) (array : _[]) : AvlTree<'T> =
        (Empty, array)
        ||> Array.fold (fun tree el ->
            insert comparer el tree)

    /// Returns a sequence containing the elements stored
    /// in an AVL tree, ordered from least to greatest.
    let rec toSeq (tree : AvlTree<'T>) =
        seq {
        match tree with
        | Empty -> ()
        | Node (n, l, r, _) ->
            yield! toSeq l
            yield n
            yield! toSeq r
        }

    /// Returns a sequence containing the elements stored in
    /// an AVL tree, ordered from greatest to least.
    let rec toSeqRev (tree : AvlTree<'T>) =
        seq {
        match tree with
        | Empty -> ()
        | Node (n, l, r, _) ->
            yield! toSeq r
            yield n
            yield! toSeq l
        }
    
    /// Returns an F# list containing the elements stored in
    /// an AVL tree, ordered from least to greatest. 
    let toList (tree : AvlTree<'T>) =
        (tree, [])
        ||> foldBack (fun el lst ->
            el :: lst)

    /// Returns an F# list containing the elements stored in
    /// an AVL tree, ordered from greatest to least.
    let toListRev (tree : AvlTree<'T>) =
        ([], tree)
        ||> fold (fun lst el ->
            el :: lst)

    /// Returns an array containing the elements stored in
    /// an AVL tree, ordered from least to greatest.
    let toArray (tree : AvlTree<'T>) =
        let elements = ResizeArray ()
        iter elements.Add tree
        elements.ToArray ()


/// Defines methods which allow a type to be "measured".
type private IMeasurer<'T> =
    inherit System.Collections.Generic.IComparer<'T>

    // "Predecessor"
    abstract Previous : x : 'T -> 'T
    // "Successor"
    abstract Next : x : 'T -> 'T
    /// A distance metric. Calculuates the "distance" from the second
    /// value to the first value (the ordering is important).
    abstract Distance : x : 'T * y : 'T -> int

//
[<Struct>]
[<DebuggerDisplay("Min = {MinValue}, Max = {MaxValue}")>]
[<StructuredFormatDisplay("[{MinValue}, {MaxValue}]")>]
type private Range<'T when 'T : comparison> =
    //
    val MinValue : 'T
    //
    val MaxValue : 'T

    //
    new (value) = {
        MinValue = value;
        MaxValue = value; }

    //
    new (rangeMin, rangeMax) =
        // Preconditions
        if rangeMin > rangeMax then
            invalidArg "rangeMax" "The minimum range value cannot be greater than the maximum range value."

        { MinValue = rangeMin;
          MaxValue = rangeMax; }

    override this.ToString () =
        sprintf "[%O, %O]" this.MinValue this.MaxValue

/// A Discrete Interval Encoding Tree (DIET).
type private Diet<'T when 'T : comparison> =
    AvlTree<Range<'T>>

/// Functional operations for DIETs.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private Diet =
    open System.Collections.Generic
    open LanguagePrimitives

    //
    module private AvlTree =
        //
        let [<Literal>] private balanceTolerance = 1u

        /// Join two trees together at a pivot point, then balance the resulting tree.
        let balance x l (r : AvlTree<'T>) =
            let hl = AvlTree.height l
            let hr = AvlTree.height r
            if hl > hr + balanceTolerance then
                match l with
                | Empty ->
                    invalidArg "AvlTree.balance" "The left subtree is empty."
                | Node (lvx, ll, lr, _) ->
                    if AvlTree.height ll >= AvlTree.height lr then
                        AvlTree.create lvx ll (AvlTree.create x lr r)
                    else
                        match lr with
                        | Empty ->
                            invalidArg "AvlTree.balance" "The right subtree is empty."
                        | Node (lrx, lrl, lrr, _)->
                            AvlTree.create lrx (AvlTree.create lvx ll lrl) (AvlTree.create x lrr r)

            else if hr > hl + balanceTolerance then
                match r with
                | Empty ->
                    invalidArg "AvlTree.balance" "The right subtree is empty."
                | Node (rvx, rl, rr, _) ->
                    if AvlTree.height rr >= AvlTree.height rl then
                        AvlTree.create rvx (AvlTree.create x l rl) rr
                    else
                        match rl with
                        | Empty ->
                            invalidArg "AvlTree.balance" "The left subtree is empty."
                        | Node (rlx, rll, rlr, _) ->
                            AvlTree.create rlx (AvlTree.create x l rll) (AvlTree.create rvx rlr rr)

            else
                Node (x, l, r, (max hl hr) + 1u)
    
        /// Join two trees together at a pivot point.
        /// The resulting tree may be unbalanced.
        let rec join v l (r : AvlTree<'T>) =
            let rec myadd left x = function
                | Empty ->
                    Node (x, Empty, Empty, 1u)
                | Node (vx, l, r, _) ->
                    if left then
                        balance vx (myadd left x l) r
                    else
                        balance vx l (myadd left x r)
        
            match l, r with
            | Empty, _ ->
                myadd true v r
            | _, Empty ->
                myadd false v l
            | Node (lx, ll, lr, lh), Node (rx, rl, rr, rh) ->
                if lh > rh + balanceTolerance then
                    balance lx ll (join v lr r)
                else if rh > lh + balanceTolerance then
                    balance rx (join v l rl) rr
                else
                    AvlTree.create v l r

        /// Reroot of balanced trees.
        let reroot (comparer : IComparer<_>) l (r : AvlTree<'T>) =
            if AvlTree.height l > AvlTree.height r then
                let i, l' = AvlTree.extractMax comparer l
                join i l' r
            else
                if AvlTree.isEmpty r then Empty
                else
                    let i, r' = AvlTree.extractMin comparer r
                    join i l r'

    //
    let inline private safe_pred (measurer : IMeasurer<_>) limit x =
        if measurer.Compare (limit, x) < 0 then
            measurer.Previous x
        else x

    //
    let inline private safe_succ (measurer : IMeasurer<_>) limit x =
        if measurer.Compare (limit, x) > 0 then
            measurer.Next x
        else x

    //
    let inline private max (measurer : IMeasurer<_>) x y =
        if measurer.Compare (x, y) > 0 then x else y

    //
    let inline private min (measurer : IMeasurer<_>) x y =
        if measurer.Compare (x, y) < 0 then x else y

    //
    let inline height (t : Diet<'T>) =
        AvlTree.height t

    //
    let rec private find_del_left_rec (measurer : IMeasurer<_>) p (tree : Diet<'T>) cont =
        match tree with
        | AvlTree.Empty ->
            cont (p, AvlTree.Empty)
        | AvlTree.Node (range, left, right, _) ->
            if measurer.Compare (p, measurer.Next range.MaxValue) > 0 then
                find_del_left_rec measurer p right <| fun (p', right') ->
                    cont (p', AvlTree.join range left right')
            elif measurer.Compare (p, range.MinValue) < 0 then
                find_del_left_rec measurer p left cont
            else
                cont (range.MinValue, left)

    //
    let private find_del_left (measurer : IMeasurer<_>) p (tree : Diet<'T>) =
        find_del_left_rec measurer p tree id

    //
    let rec private find_del_right_rec (measurer : IMeasurer<_>) p (tree : Diet<'T>) cont =
        match tree with
        | AvlTree.Empty ->
            cont (p, AvlTree.Empty)
        | AvlTree.Node (range, left, right, _) ->
            if measurer.Compare (p, measurer.Previous range.MinValue) < 0 then
                find_del_right_rec measurer p left <| fun (p', left') ->
                    cont (p', AvlTree.join range left' right)
            elif measurer.Compare (p, range.MaxValue) > 0 then
                find_del_right_rec measurer p right cont
            else
                cont (range.MaxValue, right)
    
    //
    let private find_del_right (measurer : IMeasurer<_>) p (tree : Diet<'T>) =
        find_del_right_rec measurer p tree id

    /// An empty DIET.
    let empty : Diet<'T> =
        AvlTree.empty

    /// Determines if a DIET is empty.
    let inline isEmpty (tree : Diet<'T>) =
        AvlTree.isEmpty tree

    /// Determines if a DIET contains a specified value.
    let rec contains (measurer : IMeasurer<_>) value (tree : Diet<'T>) =
        match tree with
        | Empty ->
            false
        | Node (range, left, right, _) ->
            if measurer.Compare (value, range.MinValue) < 0 then
                contains measurer value left
            elif measurer.Compare (value, range.MaxValue) > 0 then
                contains measurer value right
            else true
        
    /// Gets the maximum (greatest) value stored in the DIET.
    let maxElement (tree : Diet<'T>) =
        (AvlTree.maxElement tree).MaxValue
    
    /// Gets the minimum (least) value stored in the DIET.
    let minElement (tree : Diet<'T>) =
        (AvlTree.minElement tree).MinValue

    /// Creates a DIET containing the specified value.
    let singleton value : Diet<'T> =
        AvlTree.singleton <| Range (value)

    /// Creates a DIET containing the specified range of values.
    let ofRange minValue maxValue : Diet<'T> =
        // For compatibility with the F# range operator,
        // when minValue > minValue it's just considered
        // to be an empty range.
        if minValue >= maxValue then
            empty
        else
            Range (minValue, maxValue)
            |> AvlTree.singleton

    /// Returns the number of elements in the set.
    let count (measurer : IMeasurer<_>) (t : Diet<'T>) =
        let rec cardinal_aux acc = function
            | [] -> acc
            | AvlTree.Empty :: ts ->
                cardinal_aux acc ts
            | AvlTree.Node (range : Range<_>, left, right, _) :: ts ->
                let dist = measurer.Distance (range.MinValue, range.MaxValue)
                cardinal_aux (acc + dist + 1) (left :: right :: ts)
        
        cardinal_aux 0 [t]

    //
    let rec private addRec (measurer : IMeasurer<_>) p (tree : Diet<'T>) cont : Diet<_> =
        match tree with
        | Empty ->
            singleton p
            |> cont
        | Node (range, left, right, h) as t ->
            if measurer.Compare (p, range.MinValue) >= 0 then
                if measurer.Compare (p, range.MaxValue) <= 0 then
                    cont t

                elif measurer.Compare (p, measurer.Next range.MaxValue) > 0 then
                    addRec measurer p right <| fun right ->
                        AvlTree.join range left right
                        |> cont

                elif AvlTree.isEmpty right then
                    AvlTree.Node (Range (range.MinValue, p), left, right, h)
                    |> cont

                else
                    let range', r = AvlTree.extractMin measurer right

                    if measurer.Previous range'.MinValue = p then
                        AvlTree.join (Range (range.MinValue, range'.MaxValue)) left r
                    else
                        AvlTree.Node (Range (range.MinValue, p), left, right, h)
                    |> cont

            elif measurer.Compare (p, measurer.Previous range.MinValue) < 0 then
                addRec measurer p left <| fun left ->
                    AvlTree.join range left right
                    |> cont

            elif AvlTree.isEmpty left then
                AvlTree.Node (Range (p, range.MaxValue), left, right, h)
                |> cont

            else
                let range', l = AvlTree.extractMax measurer left
                if measurer.Next range'.MaxValue = p then
                    AvlTree.join (Range (range'.MinValue, range.MaxValue)) l right
                else
                    AvlTree.Node (Range (p, range.MaxValue), left, right, h)
                |> cont

    /// Returns a new set with the specified value added to the set.
    /// No exception is thrown if the set already contains the value.
    let add (measurer : IMeasurer<_>) p (tree : Diet<'T>) : Diet<_> =
        addRec measurer p tree id

    /// Returns a new set with the specified range of values added to the set.
    /// No exception is thrown if any of the values are already contained in the set.
    let rec addRange (measurer : IMeasurer<_>) newRange (tree : Diet<'T>) : Diet<_> =
        match tree with
        | AvlTree.Empty ->
            AvlTree.singleton newRange
        | AvlTree.Node (range, left, right, _) ->
            if measurer.Compare (newRange.MinValue, measurer.Previous range.MinValue) < 0 then
                AvlTree.join range (addRange measurer newRange left) right
            elif measurer.Compare (newRange.MinValue, measurer.Next range.MaxValue) > 0 then
                AvlTree.join range left (addRange measurer newRange right)
            else
                let x', left' =
                    if measurer.Compare (newRange.MinValue, range.MinValue) >= 0 then range.MinValue, left
                    else find_del_left measurer newRange.MinValue left

                let y', right' =
                    if measurer.Compare (newRange.MaxValue, range.MaxValue) <= 0 then range.MaxValue, right
                    else find_del_right measurer newRange.MaxValue right

                AvlTree.join (Range (x', y')) left' right'

    /// Returns a new set with the given element removed.
    /// No exception is thrown if the set doesn't contain the specified element.
    let rec remove (measurer : IMeasurer<_>) z (tree : Diet<'T>) : Diet<'T> =
        let inline compare a b =
            measurer.Compare (a, b)

        match tree with
        | AvlTree.Empty ->
            AvlTree.Empty
        | AvlTree.Node (range, left, right, h) ->
            let czx = compare z range.MinValue
            if czx < 0 then
                AvlTree.join range (remove measurer z left) right
            else
                let cyz = compare range.MaxValue z
                if cyz < 0 then
                    AvlTree.join range left (remove measurer z right)
                elif cyz = 0 then
                    if czx = 0 then
                        AvlTree.reroot measurer left right
                    else
                        let newRange = Range (range.MinValue, measurer.Previous range.MaxValue)
                        AvlTree.Node (newRange, left, right, h)
                elif czx = 0 then
                    let newRange = Range (measurer.Next range.MinValue, range.MaxValue)
                    AvlTree.Node (newRange, left, right, h)
                else
                    let newRange = Range (range.MinValue, measurer.Previous z)
                    let newRange' = Range (measurer.Next z, range.MaxValue)
                    AvlTree.Node (newRange, left, right, h)
                    |> addRange measurer newRange'

    /// Computes the union of the two sets.
    let rec union (measurer : IMeasurer<_>) (input : Diet<_>) (stream : Diet<_>) : Diet<'T> =
        let inline compare a b =
            measurer.Compare (a, b)

        let rec union' (input : Diet<_>) limit head (stream : Diet<_>) =
            match head with
            | None ->
                input, None, AvlTree.Empty
            | Some (rangeXY : Range<_>) ->
                match input with
                | AvlTree.Empty ->
                    (AvlTree.Empty, head, stream)
                | AvlTree.Node (rangeAB, left, right, _) ->
                    let left', head, stream =
                        if compare rangeXY.MinValue rangeAB.MinValue < 0 then
                            union' left (Some (measurer.Previous rangeAB.MinValue)) head stream
                        else (left, head, stream)

                    union_helper left' rangeAB right limit head stream

        and union_helper left (rangeAB : Range<_>) right limit head stream =
            match head with
            | None ->
                (AvlTree.join rangeAB left right, None, AvlTree.Empty)
            | Some (rangeXY : Range<_>) ->
                let greater_limit z =
                    match limit with
                    | None -> false
                    | Some u ->
                        compare z u >= 0
                
                if compare rangeXY.MaxValue rangeAB.MinValue < 0 && compare rangeXY.MaxValue (measurer.Previous rangeAB.MinValue) < 0 then
                    let left' = addRange measurer rangeXY left
                    let head, stream = AvlTree.tryExtractMin measurer stream
                    union_helper left' rangeAB right limit head stream

                elif compare rangeXY.MinValue rangeAB.MaxValue > 0 && compare rangeXY.MinValue (measurer.Next rangeAB.MaxValue) > 0 then
                    let right', head, stream = union' right limit head stream
                    (AvlTree.join rangeAB left right', head, stream)
                elif compare rangeAB.MaxValue rangeXY.MaxValue >= 0 then
                    let head, stream = AvlTree.tryExtractMin measurer stream
                    let newRange = Range (min measurer rangeAB.MinValue rangeXY.MinValue, rangeAB.MaxValue)
                    union_helper left newRange right limit head stream
                elif greater_limit rangeXY.MaxValue then
                    let newRange = Range (min measurer rangeAB.MinValue rangeXY.MinValue, rangeXY.MaxValue)
                    (left, Some newRange, stream)
                else
                    let (right', head, stream) =
                        let newRange = Range (min measurer rangeAB.MinValue rangeXY.MinValue, rangeXY.MaxValue)
                        union' right limit (Some newRange) stream
                    (AvlTree.reroot measurer left right', head, stream)
        
        if AvlTree.height stream > AvlTree.height input then
            union measurer stream input
        else
            #if DEBUG
            /// The minimum possible number of elements in the resulting set.
            let minPossibleResultCount =
                let inputCount = count measurer input
                let streamCount = count measurer stream
                GenericMaximum inputCount streamCount
            #endif

            let head, stream = AvlTree.tryExtractMin measurer stream
            let result, head, stream = union' input None head stream
            let result =
                match head with
                | None ->
                    result
                | Some i ->
                    AvlTree.join i result stream

            #if DEBUG
            let resultCount = count measurer result
            Debug.Assert (
                resultCount >= minPossibleResultCount,
                sprintf "The result set should not contain fewer than %i elements, but it contains only %i elements."
                    minPossibleResultCount resultCount)
            #endif

            result

    /// Computes the intersection of the two sets.
    let rec intersect (measurer : IMeasurer<_>) (input : Diet<'T>) (stream : Diet<'T>) : Diet<'T> =
        let inline compare a b =
            measurer.Compare (a, b)

        let rec inter' (input : Diet<_>) head (stream : Diet<_>) =
            match head with
            | None ->
                AvlTree.Empty, None, AvlTree.Empty
            | Some (rangeXY : Range<_>) ->
                match input with
                | AvlTree.Empty ->
                    AvlTree.Empty, head, stream
                | AvlTree.Node (rangeAB, left, right, _) ->
                    let left, head, stream =
                        if compare rangeXY.MinValue rangeAB.MinValue < 0 then
                            inter' left head stream
                        else
                            AvlTree.Empty, head, stream
                    inter_help rangeAB right left head stream

        and inter_help (rangeAB : Range<_>) (right : Diet<_>) (left : Diet<_>) head stream =
            match head with
            | None ->
                left, None, AvlTree.Empty
            | Some (rangeXY : Range<_>) ->
                if compare rangeXY.MaxValue rangeAB.MinValue < 0 then
                    if AvlTree.isEmpty stream then
                        (left, None, AvlTree.Empty)
                    else
                        let head, stream = AvlTree.extractMin measurer stream
                        inter_help rangeAB right left (Some head) stream
                elif compare rangeAB.MaxValue rangeXY.MinValue < 0 then
                    let right, head, stream = inter' right head stream
                    AvlTree.reroot measurer left right, head, stream
                elif compare rangeXY.MaxValue (safe_pred measurer rangeXY.MaxValue rangeAB.MaxValue) >= 0 then
                    let (right, head, stream) = inter' right head stream
                    let newRange = Range (max measurer rangeXY.MinValue rangeAB.MinValue, min measurer rangeXY.MaxValue rangeAB.MaxValue)
                    ((AvlTree.join newRange left right), head, stream)
                else
                    let left =
                        let newRange = Range (max measurer rangeXY.MinValue rangeAB.MinValue, rangeXY.MaxValue)
                        addRange measurer newRange left
                    let newRange = Range (measurer.Next rangeXY.MaxValue, rangeAB.MaxValue)
                    inter_help newRange right left head stream

        if AvlTree.height stream > AvlTree.height input then
            intersect measurer stream input
        elif AvlTree.isEmpty stream then
            AvlTree.Empty
        else
            let head, stream = AvlTree.extractMin measurer stream
            let result, _, _ = inter' input (Some head) stream
            result

    /// Returns a new set with the elements of the second set removed from the first.
    let difference (measurer : IMeasurer<_>) (input : Diet<'T>) (stream : Diet<'T>) : Diet<'T> =
        let inline compare a b =
            measurer.Compare (a, b)

        let rec diff' input head stream =
            match head with
            | None ->
                input, None, AvlTree.Empty
            | Some (rangeXY : Range<_>) ->
                match input with
                | AvlTree.Empty ->
                    (AvlTree.Empty, head, stream)
                | AvlTree.Node (rangeAB : Range<_>, left, right, _) ->
                    let left, head, stream =
                        if compare rangeXY.MinValue rangeAB.MinValue < 0 then
                            diff' left head stream
                        else
                            left, head, stream
                    diff_helper rangeAB right left head stream

        and diff_helper (rangeAB : Range<_>) (right : Diet<_>) (left : Diet<_>) head stream =
            match head with
            | None ->
                AvlTree.join rangeAB left right,
                None,
                AvlTree.Empty
            | Some (rangeXY : Range<_>) ->
                if compare rangeXY.MaxValue rangeAB.MinValue < 0 then
                    // [x, y] and [a, b] are disjoint
                    let head, stream = AvlTree.tryExtractMin measurer stream
                    diff_helper rangeAB right left head stream
                elif compare rangeAB.MaxValue rangeXY.MinValue < 0 then
                    // [a, b] and [x, y] are disjoint
                    let (right, head, stream) = diff' right head stream
                    (AvlTree.join rangeAB left right, head, stream)
                elif compare rangeAB.MinValue rangeXY.MinValue < 0 then
                    // [a, b] and [x, y] overlap
                    // a < x
                    let rangeXB = Range (rangeXY.MinValue, rangeAB.MaxValue)
                    let newRange = Range (rangeAB.MinValue, measurer.Previous rangeXY.MinValue)
                    let newLeft = addRange measurer newRange left
                    diff_helper rangeXB right newLeft head stream
                elif compare rangeXY.MaxValue rangeAB.MaxValue < 0 then
                    // [a, b] and [x, y] overlap
                    // y < b
                    let (head, stream) = AvlTree.tryExtractMin measurer stream
                    let newRange = Range (measurer.Next rangeXY.MaxValue, rangeAB.MaxValue)
                    diff_helper newRange right left head stream
                else
                    // [a, b] and [x, y] overlap
                    let (right, head, stream) = diff' right head stream
                    (AvlTree.reroot measurer left right, head, stream)
        
        if AvlTree.isEmpty stream then
            input
        else
            #if DEBUG
            /// The minimum possible number of elements in the resulting set.
            let minPossibleResultCount =
                let inputCount = count measurer input
                let streamCount = count measurer stream
                GenericMaximum 0 (inputCount - streamCount)
            #endif

            let head, stream' = AvlTree.extractMin measurer stream
            let result, _, _ = diff' input (Some head) stream'

            #if DEBUG
            let resultCount = count measurer result
            Debug.Assert (
                resultCount >= minPossibleResultCount,
                sprintf "The result set should not contain fewer than %i elements, but it contains only %i elements."
                    minPossibleResultCount resultCount)
            #endif

            result

    /// Comparison function for DIETs.
    let rec compare (measurer : IMeasurer<_>) (t1 : Diet<'T>) (t2 : Diet<'T>) =
        match t1, t2 with
        | Node (_,_,_,_), Node (_,_,_,_) ->
            let i1, r1 = AvlTree.extractMin measurer t1
            let i2, r2 = AvlTree.extractMin measurer t2
            let c =
                let d = measurer.Compare (i1.MinValue, i2.MinValue)
                if d <> 0 then -d
                else measurer.Compare (i1.MaxValue, i2.MaxValue)

            if c <> 0 then c
            else compare measurer r1 r2
        
        | Node (_,_,_,_), Empty -> 1
        | Empty, Empty -> 0
        | Empty, Node (_,_,_,_) -> -1

    /// Equality function for DIETs.
    let equal (measurer : IMeasurer<_>) (t1 : Diet<'T>) (t2 : Diet<'T>) =
        compare measurer t1 t2 = 0

    /// Applies the given accumulating function to all elements in a DIET.
    let fold (folder : 'State -> _ -> 'State) (measurer : IMeasurer<_>) (state : 'State) (tree : Diet<'T>) =
        let rangeFolder (state : 'State) (range : Range<_>) =
            let q = range.MaxValue
            // Fold over the items in increasing order.
            let mutable state = state
            let mutable currentItem = range.MinValue
            while currentItem <> q do
                state <- folder state currentItem
                currentItem <- measurer.Next currentItem

            // Apply the folder function to the last value in the range 'q'.
            folder state q

        AvlTree.fold rangeFolder state tree

    /// Applies the given accumulating function to all elements in a DIET.
    let foldBack (folder : _ -> 'State -> 'State) (measurer : IMeasurer<_>) (tree : Diet<'T>) (state : 'State) =
        let rangeFolder (range : Range<_>) (state : 'State) =
            let p = range.MinValue

            // Fold over the items in decreasing order.
            let mutable state = state
            let mutable currentItem = range.MaxValue
            while currentItem <> p do
                state <- folder currentItem state
                currentItem <- measurer.Previous currentItem

            // Apply the folder function to the first value in the range 'p'.
            folder p state

        AvlTree.foldBack rangeFolder tree state

    /// Returns the number of intervals in the set.
    let intervalCount (t : Diet<'T>) =
        let rec cardinal_aux acc = function
            | [] -> acc
            | AvlTree.Empty :: ts ->
                cardinal_aux acc ts
            | AvlTree.Node (range : Range<_>, left, right, _) :: ts ->
                cardinal_aux (acc + 1) (left :: right :: ts)
        
        cardinal_aux 0 [t]

    //
    let rec split (measurer : IMeasurer<_>) x (tree : Diet<'T>) =
        let inline compare a b =
            measurer.Compare (a, b)

        match tree with
        | AvlTree.Empty ->
            AvlTree.Empty, false, AvlTree.Empty
        | AvlTree.Node (rangeAB : Range<_>, l, r, _) ->
            let cxa = compare x rangeAB.MinValue
            if cxa < 0 then
                let ll, pres, rl = split measurer x l
                ll, pres, AvlTree.join rangeAB rl r
            else
                let cbx = compare rangeAB.MaxValue x
                if cbx < 0 then
                    let lr, pres, rr = split measurer x r
                    AvlTree.join rangeAB l lr, pres, rr
                else
                    ((if cxa = 0 then l else addRange measurer (Range (rangeAB.MinValue, measurer.Previous x)) l),
                       true,
                       (if cbx = 0 then r else addRange measurer (Range (measurer.Next x, rangeAB.MaxValue)) r))

    /// Builds a new DIET from the elements of a sequence.
    let ofSeq (measurer : IMeasurer<_>) (sequence : seq<_>) : Diet<'T> =
        (Empty, sequence)
        ||> Seq.fold (fun tree el ->
            add measurer el tree)

    /// Builds a new DIET from the elements of an F# list.
    let ofList (measurer : IMeasurer<_>) (list : _ list) : Diet<'T> =
        (Empty, list)
        ||> List.fold (fun tree el ->
            add measurer el tree)

    /// Builds a new DIET from the elements of an array.
    let ofArray (measurer : IMeasurer<_>) (array : _[]) : Diet<'T> =
        (Empty, array)
        ||> Array.fold (fun tree el ->
            add measurer el tree)

    //
    let forall (predicate : 'T -> bool) (measurer : IMeasurer<_>) (t : Diet<'T>) =
        // OPTIMIZE : Rewrite this to short-circuit and return early
        // if we find a non-matching element.
        (measurer, true, t)
        |||> fold (fun state el ->
            state && predicate el)


/// Character set implementation based on a Discrete Interval Encoding Tree.
/// This is faster and more efficient than the built-in F# Set<'T>,
/// especially for dense sets.
[<DebuggerDisplay("Count = {Count}, Intervals = {IntervalCount}")>]
type CharSet private (dietSet : Diet<char>) =
    //
    static let empty = CharSet (Diet.empty)

    //
    static let charComparer =
        LanguagePrimitives.FastGenericComparer<char>

    //
    static let charMeasurer = {
        new IMeasurer<char> with
            member __.Compare (x, y) =
                charComparer.Compare (x, y)
            member __.Previous x =
                char <| (uint16 x) - 1us
            member __.Next x =
                char <| (uint16 x) + 1us
            member __.Distance (x, y) =
                int y - int x }

    //
    static member Empty
        with get () = empty
    
    override __.GetHashCode () =
        // TODO : Come up with a better hashcode function.
        (Diet.count charMeasurer dietSet) * (int <| AvlTree.height dietSet)
    
    override __.Equals other =
        match other with
        | :? CharSet as other ->
            Diet.equal charMeasurer dietSet other.DietSet
        | _ ->
            false

    //
    member private __.DietSet
        with get () = dietSet

    //
    member __.Count
        with get () =
            Diet.count charMeasurer dietSet

    //
    member __.IntervalCount
        with get () =
            Diet.intervalCount dietSet

    //
    member __.MaxElement
        with get () =
            Diet.maxElement dietSet

    //
    member __.MinElement
        with get () =
            Diet.minElement dietSet

    /// The set containing the given element.
    static member FromElement value =
        CharSet (Diet.singleton value)

    /// The set containing the elements in the given range.
    static member FromRange (lowerBound, upperBound) =
        CharSet (Diet.ofRange lowerBound upperBound)

    //
    static member IsEmpty (charSet : CharSet) =
        Diet.isEmpty charSet.DietSet

    /// Returns a new set with an element added to the set.
    /// No exception is raised if the set already contains the given element.
    static member Add (value, charSet : CharSet) =
        CharSet (Diet.add charMeasurer value charSet.DietSet)

    //
    static member AddRange (lower, upper, charSet : CharSet) =
        CharSet (Diet.addRange charMeasurer (Range (lower, upper)) charSet.DietSet)

    //
    static member Remove (value, charSet : CharSet) =
        CharSet (Diet.remove charMeasurer value charSet.DietSet)

    //
    static member Contains (value, charSet : CharSet) =
        Diet.contains charMeasurer value charSet.DietSet

//    //
//    static member ToList (charSet : CharSet) =
//        Diet.toList charSet.DietSet

    //
    static member OfList list =
        CharSet (Diet.ofList charMeasurer list)

//    //
//    static member ToSet (charSet : CharSet) =
//        Diet.toSet charSet.DietSet

//    //
//    static member OfSet set =
//        CharSet (Diet.ofSet charMeasurer set)

//    //
//    static member ToArray (charSet : CharSet) =
//        Diet.toArray charSet.DietSet
    
    //
    static member OfArray array =
        CharSet (Diet.ofArray charMeasurer array)

//    //
//    static member ToSequence (charSet : CharSet) =
//        Diet.toSeq charSet.DietSet

    //
    static member OfSequence sequence =
        CharSet (Diet.ofSeq charMeasurer sequence)

    //
    static member Difference (charSet1 : CharSet, charSet2 : CharSet) =
        CharSet (Diet.difference charMeasurer charSet1.DietSet charSet2.DietSet)

    //
    static member Intersect (charSet1 : CharSet, charSet2 : CharSet) =
        CharSet (Diet.intersect charMeasurer charSet1.DietSet charSet2.DietSet)

    //
    static member Union (charSet1 : CharSet, charSet2 : CharSet) =
        CharSet (Diet.union charMeasurer charSet1.DietSet charSet2.DietSet)

    //
    static member Fold (folder : 'State -> _ -> 'State, state, charSet : CharSet) =
        Diet.fold folder charMeasurer state charSet.DietSet

    //
    static member FoldBack (folder : _ -> 'State -> 'State, state, charSet : CharSet) =
        Diet.foldBack folder charMeasurer charSet.DietSet state

    //
    static member Forall (predicate, charSet : CharSet) =
        Diet.forall predicate charMeasurer charSet.DietSet

    //
    static member IterateIntervals (action, charSet : CharSet) =
        let action = FSharpFunc<_,_,_>.Adapt action
        charSet.DietSet
        |> AvlTree.iter (fun interval ->
            action.Invoke (interval.MinValue, interval.MaxValue))

    interface System.IComparable with
        member this.CompareTo other =
            match other with
            | :? CharSet as other ->
                Diet.compare charMeasurer this.DietSet other.DietSet
            | _ ->
                invalidArg "other" "The argument is not an instance of CharSet."

    interface System.IComparable<CharSet> with
        member this.CompareTo other =
            Diet.compare charMeasurer dietSet other.DietSet

    interface System.IEquatable<CharSet> with
        member this.Equals other =
            Diet.equal charMeasurer dietSet other.DietSet


/// Functional programming operators related to the CharSet type.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module CharSet =
    /// The empty set.
    let empty = CharSet.Empty

    /// Returns 'true' if the set is empty.
    let isEmpty charSet =
        CharSet.IsEmpty charSet

    /// The set containing the given element.
    let inline singleton c =
        CharSet.FromElement c

    /// The set containing the elements in the given range.
    let inline ofRange lowerBound upperBound =
        CharSet.FromRange (lowerBound, upperBound)

    /// Returns the number of elements in the set.
    let inline count (charset : CharSet) =
        charset.Count

    /// Returns the number of intervals in the set.
    let inline intervalCount (charset : CharSet) =
        charset.IntervalCount

    /// Returns a new set with an element added to the set.
    /// No exception is raised if the set already contains the given element.
    let inline add value charSet =
        CharSet.Add (value, charSet)

    //
    let inline addRange lower upper charSet =
        CharSet.AddRange (lower, upper, charSet)

    /// Returns a new set with the given element removed.
    /// No exception is raised if the set doesn't contain the given element.
    let inline remove value charSet =
        CharSet.Remove (value, charSet)

    /// Evaluates to 'true' if the given element is in the given set.
    let inline contains value charSet =
        CharSet.Contains (value, charSet)

    /// Applies the given accumulating function to all the elements of the set.
    let inline fold (folder : 'State -> char -> 'State) (state : 'State) charSet =
        CharSet.Fold (folder, state, charSet)

    /// Applies the given accumulating function to all the elements of the set.
    let inline foldBack (folder : char -> 'State -> 'State) charSet (state : 'State) =
        CharSet.FoldBack (folder, state, charSet)

//    /// Returns a new set containing the results of applying the given function to each element of the input set.
//    let map (mapping : char -> char) charSet =
//        (empty, charSet)
//        ||> fold (fun set el ->
//            add (mapping el) set)
//
//    /// Returns a new set containing only the elements of the collection for which the given predicate returns true.
//    let filter (predicate : char -> bool) charSet =
//        (empty, charSet)
//        ||> fold (fun set el ->
//            if predicate el then
//                add el set
//            else set)
//
//    /// Applies the given function to each element of the set, in order from least to greatest.
//    let iter (action : char -> unit) charSet =
//        iterImpl action charSet id

    /// Applies the given function to each element of the set, in order from least to greatest.
    let inline iterIntervals action charSet =
        CharSet.IterateIntervals (action, charSet)

//    /// Tests if any element of the collection satisfies the given predicate.
//    /// If the input function is <c>predicate</c> and the elements are <c>i0...iN</c>,
//    /// then this function computes predicate <c>i0 or ... or predicate iN</c>.
//    let exists (predicate : char -> bool) charSet =
//        existsImpl predicate charSet id

    /// Tests if all elements of the collection satisfy the given predicate.
    /// If the input function is <c>p</c> and the elements are <c>i0...iN</c>,
    /// then this function computes <c>p i0 && ... && p iN</c>.
    let inline forall (predicate : char -> bool) charSet =
        CharSet.Forall (predicate, charSet)

//    /// Creates a list that contains the elements of the set in order.
//    let inline toList charSet =
//        // Fold backwards so we don't need to reverse the list.
//        (tree, [])
//        ||> foldBack (fun i lst ->
//            i :: lst)

    /// Creates a set that contains the same elements as the given list.
    let inline ofList list =
        CharSet.OfList list

//    /// Creates a Set that contains the same elements as the given CharSet.
//    let toSet charSet =
//        (Set.empty, tree)
//        ||> fold (fun set el ->
//            Set.add el set)
//
//    /// Creates a CharSet that contains the same elements as the given Set.
//    let ofSet set =
//        (empty, set)
//        ||> Set.fold (fun tree el ->
//            add el tree)

//    /// Creates an array that contains the elements of the set in order.
//    let toArray charSet =
//        let resizeArr = ResizeArray<_> ()
//        iter resizeArr.Add tree
//        resizeArr.ToArray ()

    /// Creates a set that contains the same elements as the given array.
    let inline ofArray array =
        CharSet.OfArray array

//    /// Returns an ordered view of the set as an enumerable object.
//    let rec toSeq charSet =
//        seq {
//        match tree with
//        | Empty -> ()
//        | Node (lowerBound, upperBound, left, right) ->
//            // Produce the sequence for the left subtree.
//            yield! toSeq left
//
//            // Produce the sequence of values in this interval.
//            yield! { lowerBound .. upperBound }
//
//            // Produce the sequence for the right subtree.
//            yield! toSeq right }

    /// Creates a new set from the given enumerable object.
    let inline ofSeq seq =
        CharSet.OfSequence seq

    /// Returns the highest (greatest) value in the set.
    let inline maxElement (charSet : CharSet) =
        charSet.MaxElement

    /// Returns the lowest (least) value in the set.
    let inline minElement (charSet : CharSet) =
        charSet.MinElement

//    /// Splits the set into two sets containing the elements for which
//    /// the given predicate returns true and false respectively.
//    let partition predicate charSet =
//        ((empty, empty), set)
//        ||> fold (fun (trueSet, falseSet) el ->
//            if predicate el then
//                add el trueSet,
//                falseSet
//            else
//                trueSet,
//                add el falseSet)

    /// Returns a new set with the elements of the second set removed from the first.
    let inline difference set1 set2 =
        CharSet.Difference (set1, set2)

    /// Computes the intersection of the two sets.
    let inline intersect set1 set2 =
        CharSet.Intersect (set1, set2)

    /// Computes the union of the two sets.
    let inline union set1 set2 =
        CharSet.Union (set1, set2)


