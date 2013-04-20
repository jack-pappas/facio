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
open System.Diagnostics
open OptimizedClosures
open ExtCore
open ExtCore.Collections
open ExtCore.Control


[<AutoOpen>]
module internal Constants =
    //
    let [<Literal>] defaultStackCapacity = 16
    //
    let [<Literal>] balanceTolerance = 2u   //1u


(*  NOTE :  The core functions implementing the AVL tree algorithm were extracted into OCaml
            from the "AVL Trees" theory in the Archive of Formal Proofs:
                http://afp.sourceforge.net/entries/AVL-Trees.shtml
            using Isabelle/HOL 2012. The extracted code was adapted to F# (e.g., by adjusting
            the formatting, fixing incomplete pattern-matches), then the supporting functions
            (e.g., 'fold', 'iter') were implemented.
            
            The DIET code was ported from Friedmann and Lange's 'camldiets' code, which is
            based on their paper "More on Balanced Diets". Their code was adapted to F# and
            the AVL tree extracted from Isabelle/HOL, then specialized for the 'char' type. *)

/// AVL Tree.
[<NoEquality; NoComparison>]
[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
type internal AvlTree<'T when 'T : comparison> =
    /// Empty tree.
    | Empty
    /// Node.
    // Left-Child, Right-Child, Value, Height
    | Node of AvlTree<'T> * AvlTree<'T> * 'T * uint32

    /// Implementation. Returns the height of a AvlTree.
    static member private ComputeHeightRec (tree : AvlTree<'T>) cont =
        match tree with
        | Empty ->
            cont 0u
        | Node (l, r, _, _) ->
            AvlTree.ComputeHeightRec l <| fun height_l ->
            AvlTree.ComputeHeightRec r <| fun height_r ->
                (max height_l height_r) + 1u
                |> cont

    /// Returns the height of a AvlTree.
    static member private ComputeHeight (tree : AvlTree<'T>) =
        AvlTree.ComputeHeightRec tree id
        
    /// Determines if a AvlTree is correctly formed.
    /// It isn't necessary to call this at run-time, though it may be useful for asserting
    /// the correctness of functions which weren't extracted from the Isabelle/HOL theory.
    static member private AvlInvariant (tree : AvlTree<'T>) =
        match tree with
        | Empty -> true
        | Node (l, r, x, h) ->
            let height_l = AvlTree.ComputeHeight l
            let height_r = AvlTree.ComputeHeight r
            height_l = height_r
            || (height_l = (1u + height_r) || height_r = (1u + height_l))
            && h = ((max height_l height_r) + 1u)
            && AvlTree.AvlInvariant l
            && AvlTree.AvlInvariant r

    /// Returns the height of a AvlTree.
    static member inline Height (tree : AvlTree<'T>) =
        match tree with
        | Empty -> 0u
        | Node (_,_,_,h) -> h

    /// Determines if a AvlTree is empty.
    static member inline IsEmptyTree (tree : AvlTree<'T>) =
        match tree with
        | Empty -> true
        | Node (_,_,_,_) -> false

    /// Creates a AvlTree whose root node holds the specified value
    /// and the specified left and right subtrees.
    static member inline Create (value, l, r : AvlTree<'T>) =
        Node (l, r, value, (max (AvlTree.Height l) (AvlTree.Height r)) + 1u)

    /// Creates a AvlTree containing the specified value.
    static member Singleton value : AvlTree<'T> =
        AvlTree.Create (value, Empty, Empty)

    static member private mkt_bal_l (n, l, r : AvlTree<'T>) =
        if AvlTree.Height l = AvlTree.Height r + balanceTolerance then
            match l with
            | Empty ->
                failwith "mkt_bal_l"
            | Node (ll, lr, ln, _) ->
                if AvlTree.Height ll < AvlTree.Height lr then
                    match lr with
                    | Empty ->
                        failwith "mkt_bal_l"
                    | Node (lrl, lrr, lrn, _) ->
                        AvlTree.Create (lrn, AvlTree.Create (ln, ll, lrl), AvlTree.Create (n, lrr, r))
                else
                    AvlTree.Create (ln, ll, AvlTree.Create (n, lr, r))
        else
            AvlTree.Create (n, l, r)

    static member private mkt_bal_r (n, l, r : AvlTree<'T>) =
        if AvlTree.Height r = AvlTree.Height l + balanceTolerance then
            match r with
            | Empty ->
                failwith "mkt_bal_r"
            | Node (rl, rr, rn, _) ->
                if AvlTree.Height rr < AvlTree.Height rl then
                    match rl with
                    | Empty ->
                        failwith "mkt_bal_r"
                    | Node (rll, rlr, rln, _) ->
                        AvlTree.Create (rln, AvlTree.Create (n, l, rll), AvlTree.Create (rn, rlr, rr))
                else
                    AvlTree.Create (rn, AvlTree.Create (n, l, rl), rr)
        else
            AvlTree.Create (n, l, r)

    static member DeleteMax (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "Cannot delete the maximum value from an empty tree."
        | Node (l, Empty, n, _) ->
            n, l
        | Node (l, (Node (_,_,_,_) as right), n, _) ->
            let na, r = AvlTree.DeleteMax right
            na, AvlTree.mkt_bal_l (n, l, r)

    static member DeleteRoot (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "Cannot delete the root of an empty tree."
        | Node (Empty, r, _, _) -> r
        | Node ((Node (_,_,_,_) as left), Empty, _, _) ->
            left
        | Node ((Node (_,_,_,_) as left), (Node (_,_,_,_) as right), _, _) ->
            let new_n, l = AvlTree.DeleteMax left
            AvlTree.mkt_bal_r (new_n, l, right)

    /// Determines if a AvlTree contains a specified value.
    static member Contains (comparer : IComparer<'T>, tree : AvlTree<'T>, value : 'T) =
        match tree with
        | Empty ->
            false
        | Node (l, r, n, _) ->
            let comparison = comparer.Compare (value, n)
            if comparison = 0 then      // value = n
                true
            elif comparison < 0 then    // value < n
                AvlTree.Contains (comparer, l, value)
            else                        // value > n
                AvlTree.Contains (comparer, r, value)

    /// Removes the specified value from the tree.
    /// If the tree doesn't contain the value, no exception is thrown;
    /// the tree will be returned without modification.
    static member Delete (comparer : IComparer<'T>, tree : AvlTree<'T>, value : 'T) =
        match tree with
        | Empty ->
            Empty
        | Node (l, r, n, _) ->
            let comparison = comparer.Compare (value, n)
            if comparison = 0 then              // x = n
                AvlTree.DeleteRoot tree
            elif comparison < 0 then            // x < n
                let la = AvlTree.Delete (comparer, l, value)
                AvlTree.mkt_bal_r (n, la, r)
            else                                // x > n
                let a = AvlTree.Delete (comparer, r, value)
                AvlTree.mkt_bal_l (n, l, a)

    /// Adds a value to a AvlTree.
    /// If the tree already contains the value, no exception is thrown;
    /// the tree will be returned without modification.
    static member Insert (comparer : IComparer<'T>, tree : AvlTree<'T>, value : 'T) =
        match tree with
        | Empty ->
            Node (Empty, Empty, value, 1u)
        | Node (l, r, n, _) ->
            let comparison = comparer.Compare (value, n)
            if comparison = 0 then                              // x = n
                tree
            elif comparison < 0 then                            // x < n
                let l' = AvlTree.Insert (comparer, l, value)
                AvlTree.mkt_bal_l (n, l', r)
            else                                                // x > n
                let r' = AvlTree.Insert (comparer, r, value)
                AvlTree.mkt_bal_r (n, l, r')

    /// Gets the maximum (greatest) value stored in the AvlTree.
    static member MaxElement (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (_, Empty, n, _) ->
            n
        | Node (_, right, _, _) ->
            AvlTree.MaxElement right

    /// Gets the minimum (least) value stored in the AvlTree.
    static member MinElement (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (Empty, _, n, _) ->
            n
        | Node (left, _, _, _) ->
            AvlTree.MinElement left

    /// Extracts the minimum (least) value from a AvlTree,
    /// returning the value along with the updated tree.
    static member ExtractMin (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (Empty, r, n, _) ->
            n, r
        | Node (Node (left, mid, a, _), r, x, _) ->
            // Rebalance the tree at the same time we're traversing downwards
            // to find the minimum value. This avoids the need to perform a
            // second traversal to remove the element once it's found.
            let n = AvlTree.Create (x, mid, r)
            AvlTree.Create (a, left, n)
            |> AvlTree.ExtractMin

    /// Extracts the minimum (least) value from a AvlTree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    static member TryExtractMin (tree : AvlTree<'T>) =
        // Is the tree empty?
        if AvlTree.IsEmptyTree tree then
            None, tree
        else
            let minElement, tree = AvlTree.ExtractMin tree
            Some minElement, tree

    /// Extracts the maximum (greatest) value from a AvlTree,
    /// returning the value along with the updated tree.
    static member ExtractMax (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (l, Empty, n, _) ->
            n, l
        | Node (l, Node (mid, right, a, _), x, _) ->
            // Rebalance the tree at the same time we're traversing downwards
            // to find the maximum value. This avoids the need to perform a
            // second traversal to remove the element once it's found.
            let n = AvlTree.Create (x, l, mid)
            AvlTree.Create (a, n, right)
            |> AvlTree.ExtractMax

    /// Extracts the maximum (greatest) value from a AvlTree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    static member TryExtractMax (tree : AvlTree<'T>) =
        // Is the tree empty?
        if AvlTree.IsEmptyTree tree then
            None, tree
        else
            let maxElement, tree = AvlTree.ExtractMax tree
            Some maxElement, tree

    /// Counts the number of elements in the tree.
    static member Count (tree : AvlTree<'T>) =
        match tree with
        | Empty -> 0u
        | Node (Empty, Empty, _, _) -> 1u
        | Node (l, r, _, _) ->
            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// The number of elements discovered in the tree so far.
            let mutable count = 1u   // Start at one (1) to include this root node.

            // Traverse the tree using the mutable stack, incrementing the counter at each node.
            stack.Push r
            stack.Push l

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                (* OPTIMIZATION: Handle a few of the cases specially here to avoid pushing empty
                   nodes on the stack. *)
                | Node (Empty, Empty, _, _) ->
                    // Increment the element count.
                    count <- count + 1u

                | Node (Empty, z, _, _)
                | Node (z, Empty, _, _) ->
                    // Increment the element count.
                    count <- count + 1u

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, _, _) ->
                    // Increment the element count.
                    count <- count + 1u

                    // Push the children onto the stack.
                    stack.Push r
                    stack.Push l

            // Return the element count.
            count

    //
    static member Iter (action : 'T -> unit) (tree : AvlTree<'T>) : unit =
        match tree with
        | Empty -> ()
        | Node (Empty, Empty, x, _) ->
            // Invoke the action with this single element.
            action x
        | Node (l, r, x, _) ->
            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push r
            stack.Push <| AvlTree.Singleton x
            stack.Push l

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, x, _) ->
                    // Apply this value to the action function.
                    action x

                | Node (Empty, z, x, _) ->
                    // Apply this value to the action function.
                    action x

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, x, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| AvlTree.Singleton x
                    stack.Push l

    /// Applies the given accumulating function to all elements in a AvlTree.
    static member Fold (folder : 'State -> 'T -> 'State) (state : 'State) (tree : AvlTree<'T>) =
        match tree with
        | Empty -> state
        | Node (Empty, Empty, x, _) ->
            // Invoke the folder function on this single element and return the result.
            folder state x
        | Node (l, r, x, _) ->
            // Adapt the folder function since we'll always supply all of the arguments at once.
            let folder = FSharpFunc<_,_,_>.Adapt folder

            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// The current state value.
            let mutable state = state

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push r
            stack.Push <| AvlTree.Singleton x
            stack.Push l

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, x, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (state, x)

                | Node (Empty, z, x, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (state, x)

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, x, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| AvlTree.Singleton x
                    stack.Push l

            // Return the final state value.
            state

    /// Applies the given accumulating function to all elements in a AvlTree.
    static member FoldBack (folder : 'T -> 'State -> 'State) (state : 'State) (tree : AvlTree<'T>) =
        match tree with
        | Empty -> state
        | Node (Empty, Empty, x, _) ->
            // Invoke the folder function on this single element and return the result.
            folder x state
        | Node (l, r, x, _) ->
            // Adapt the folder function since we'll always supply all of the arguments at once.
            let folder = FSharpFunc<_,_,_>.Adapt folder

            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// The current state value.
            let mutable state = state

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push l
            stack.Push <| AvlTree.Singleton x
            stack.Push r

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, x, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (x, state)

                | Node (z, Empty, x, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (x, state)

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, x, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push l
                    stack.Push <| AvlTree.Singleton x
                    stack.Push r

            // Return the final state value.
            state

    /// Tests if any element of the collection satisfies the given predicate.
    static member Exists (predicate : 'T -> bool) (tree : AvlTree<'T>) : bool =
        match tree with
        | Empty -> false
        | Node (Empty, Empty, x, _) ->
            // Apply the predicate function to this element and return the result.
            predicate x
        | Node (l, r, x, _) ->
            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// Have we found a matching element?
            let mutable foundMatch = false

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push r
            stack.Push <| AvlTree.Singleton x
            stack.Push l

            while stack.Count > 0 && not foundMatch do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, x, _) ->
                    // Apply the predicate to this element.
                    foundMatch <- predicate x

                | Node (Empty, z, x, _) ->
                    // Apply the predicate to this element.
                    foundMatch <- predicate x

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, x, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| AvlTree.Singleton x
                    stack.Push l

            // Return the value indicating whether or not a matching element was found.
            foundMatch

    /// Tests if all elements of the collection satisfy the given predicate.
    static member Forall (predicate : 'T -> bool) (tree : AvlTree<'T>) : bool =
        match tree with
        | Empty -> true
        | Node (Empty, Empty, x, _) ->
            // Apply the predicate function to this element and return the result.
            predicate x
        | Node (l, r, x, _) ->
            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// Have all of the elements we've seen so far matched the predicate?
            let mutable allElementsMatch = true

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push r
            stack.Push <| AvlTree.Singleton x
            stack.Push l

            while stack.Count > 0 && allElementsMatch do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, x, _) ->
                    // Apply the predicate to this element.
                    allElementsMatch <- predicate x

                | Node (Empty, z, x, _) ->
                    // Apply the predicate to this element.
                    allElementsMatch <- predicate x

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, x, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| AvlTree.Singleton x
                    stack.Push l

            // Return the value indicating if all elements matched the predicate.
            allElementsMatch

    /// Returns a sequence containing the elements stored
    /// in a AvlTree, ordered from least to greatest.
    static member ToSeq (tree : AvlTree<'T>) =
        seq {
        match tree with
        | Empty -> ()
        | Node (l, r, n, _) ->
            yield! AvlTree.ToSeq l
            yield n
            yield! AvlTree.ToSeq r
        }

    /// Returns a list containing the elements stored in
    /// a AvlTree, ordered from least to greatest. 
    static member ToList (tree : AvlTree<'T>) =
        ([], tree)
        ||> AvlTree.FoldBack (fun el lst ->
            el :: lst)

    /// Returns an array containing the elements stored in
    /// a AvlTree, ordered from least to greatest.
    static member ToArray (tree : AvlTree<'T>) =
        let elements = ResizeArray ()
        AvlTree.Iter elements.Add tree
        elements.ToArray ()

    //
    // TODO : This could be replaced by 'mkt_bal_l' and 'mkt_bal_r'.
    static member Rebalance (t1, t2, k) : AvlTree<'T> =
        let t1h = AvlTree.Height t1
        let t2h = AvlTree.Height t2
        if t2h > t1h + balanceTolerance then // right is heavier than left
            match t2 with
            | Node (t2l, t2r, t2k, _) ->
                // one of the nodes must have height > height t1 + 1
                if AvlTree.Height t2l > t1h + 1u then  // balance left: combination
                    match t2l with
                    | Node (t2ll, t2lr, t2lk, _) ->
                        AvlTree.Create (
                            t2lk,
                            AvlTree.Create (k, t1, t2ll),
                            AvlTree.Create (t2k, t2lr, t2r))
                    | _ -> failwith "rebalance"
                else // rotate left
                    AvlTree.Create (
                        t2k,
                        AvlTree.Create (k, t1, t2l),
                        t2r)
            | _ -> failwith "rebalance"

        elif t1h > t2h + balanceTolerance then // left is heavier than right
            match t1 with
            | Node (t1l, t1r, t1k, _) ->
                // one of the nodes must have height > height t2 + 1
                if AvlTree.Height t1r > t2h + 1u then
                    // balance right: combination
                    match t1r with
                    | Node (t1rl, t1rr, t1rk, _) ->
                        AvlTree.Create (
                            t1rk,
                            AvlTree.Create (t1k, t1l, t1rl),
                            AvlTree.Create (k, t1rr, t2))
                    | _ -> failwith "rebalance"
                else
                    AvlTree.Create (
                        t1k,
                        t1l,
                        AvlTree.Create (k, t1r, t2))
            | _ -> failwith "rebalance"

        else
            AvlTree.Create (k, t1, t2)

    //
    static member Balance (comparer : IComparer<'T>, t1, t2, k) =
        // Given t1 < k < t2 where t1 and t2 are "balanced",
        // return a balanced tree for <t1,k,t2>.
        // Recall: balance means subtrees heights differ by at most "tolerance"
        match t1, t2 with
        // TODO : The first two patterns can be merged to use the same handler.
        | Empty, t2 ->
            // drop t1 = empty
            AvlTree.Insert (comparer, t2, k)
        | t1, Empty ->
            // drop t2 = empty
            AvlTree.Insert (comparer, t1, k)

        // TODO : The next two patterns can be merged to use the same handler.
        | Node (Empty, Empty, k1, _), t2 ->
            let t' = AvlTree.Insert (comparer, t2, k1)
            AvlTree.Insert (comparer, t', k)
        | t1, Node (Empty, Empty, k2, _) ->
            let t' = AvlTree.Insert (comparer, t1, k2)
            AvlTree.Insert (comparer, t', k)

        | Node (t11, t12, k1, h1), Node (t21, t22, k2, h2) ->
            // Have:  (t11 < k1 < t12) < k < (t21 < k2 < t22)
            // Either (a) h1,h2 differ by at most 2 - no rebalance needed.
            //        (b) h1 too small, i.e. h1+2 < h2
            //        (c) h2 too small, i.e. h2+2 < h1
            if   h1+balanceTolerance < h2 then
                // case: b, h1 too small
                // push t1 into low side of t2, may increase height by 1 so rebalance
                AvlTree.Rebalance (AvlTree.Balance (comparer, t1, t21, k), t22, k2)
            elif h2+balanceTolerance < h1 then
                // case: c, h2 too small
                // push t2 into high side of t1, may increase height by 1 so rebalance
                AvlTree.Rebalance (t11, AvlTree.Balance (comparer, t12, t2, k), k1)
            else
                // case: a, h1 and h2 meet balance requirement
                AvlTree.Create (k, t1, t2)

    //
    static member Split (comparer : IComparer<'T>, t, pivot) : AvlTree<'T> * bool * AvlTree<'T> =
        // Given a pivot and a set t
        // Return { x in t s.t. x < pivot }, pivot in t? , { x in t s.t. x > pivot }
        match t with
        | Empty  ->
            Empty, false, Empty
        | Node (Empty, Empty, k1, _) ->
            let c = comparer.Compare (k1, pivot)
            if   c < 0 then t    ,false,Empty // singleton under pivot
            elif c = 0 then Empty,true ,Empty // singleton is    pivot
            else            Empty,false,t     // singleton over  pivot
        | Node (t11, t12, k1, _) ->
            let c = comparer.Compare (pivot, k1)
            if   c < 0 then // pivot t1
                let t11Lo, havePivot, t11Hi = AvlTree.Split (comparer, t11, pivot)
                t11Lo, havePivot, AvlTree.Balance (comparer, t11Hi, t12, k1)
            elif c = 0 then // pivot is k1
                t11,true,t12
            else            // pivot t2
                let t12Lo, havePivot, t12Hi = AvlTree.Split (comparer, t12, pivot)
                AvlTree.Balance (comparer, t11, t12Lo, k1), havePivot, t12Hi

    static member private CompareStacks (comparer : IComparer<'T>, l1 : AvlTree<'T> list, l2 : AvlTree<'T> list) : int =
        match l1, l2 with
        | [], [] -> 0
        | [], _ -> -1
        | _, [] -> 1
        | (Empty :: t1), (Empty :: t2) ->
            AvlTree.CompareStacks (comparer, t1, t2)
        | (Node (Empty, Empty, n1k, _) :: t1), (Node (Empty, Empty, n2k, _) :: t2) ->
            match comparer.Compare (n1k, n2k) with
            | 0 ->
                AvlTree.CompareStacks (comparer, t1, t2)
            | c -> c

        | (Node (Empty, Empty, n1k, _) :: t1), (Node (Empty, n2r, n2k, _) :: t2) ->
            match comparer.Compare (n1k, n2k) with
            | 0 ->
                AvlTree.CompareStacks (comparer, Empty :: t1, n2r :: t2)
            | c -> c

        | (Node (Empty, n1r, n1k, _) :: t1), (Node (Empty, Empty, n2k, _) :: t2) ->
            match comparer.Compare (n1k, n2k) with
            | 0 ->
                AvlTree.CompareStacks (comparer, n1r :: t1, Empty :: t2)
            | c -> c

        | (Node (Empty, n1r, n1k, _) :: t1), (Node (Empty, n2r, n2k, _) :: t2) ->
            match comparer.Compare (n1k, n2k) with
            | 0 ->
                AvlTree.CompareStacks (comparer, n1r :: t1, n2r :: t2)
            | c -> c

        | ((Node (Empty, Empty, n1k, _) :: t1) as l1), _ ->
            AvlTree.CompareStacks (comparer, Empty :: l1, l2)
        
        | (Node (n1l, n1r, n1k, _) :: t1), _ ->
            AvlTree.CompareStacks (comparer, n1l :: Node (Empty, n1r, n1k, 0u) :: t1, l2)
        
        | _, ((Node (Empty, Empty, n2k, _) :: t2) as l2) ->
            AvlTree.CompareStacks (comparer, l1, Empty :: l2)
        
        | _, (Node (n2l, n2r, n2k, _) :: t2) ->
            AvlTree.CompareStacks (comparer, l1, n2l :: Node (Empty, n2r, n2k, 0u) :: t2)
                
    static member Compare (comparer : IComparer<'T>, s1 : AvlTree<'T>, s2 : AvlTree<'T>) : int =
        match s1, s2 with
        | Empty, Empty -> 0
        | Empty, _ -> -1
        | _, Empty -> 1
        | _ ->
            AvlTree<'T>.CompareStacks (comparer, [s1], [s2])

    /// Join two trees together with the specified root element.
    /// Takes two trees representing disjoint sets and combines them, returning
    /// a new balanced tree representing the union of the two sets and the given root element.
    /// The resulting tree may be unbalanced.
        // NOTE : Are we sure about this? It looks like the resulting tree will _always_
        // be balanced in this implementation.
    static member Join comparer root l (r : AvlTree<'T>) =
        match l, r with
        | Empty, Empty ->
            AvlTree.Singleton root
        | Empty, _ ->
            AvlTree.Insert (comparer, r, root)
        | _, Empty ->
            AvlTree.Insert (comparer, l, root)
        | Node (ll, lr, lx, lh), Node (rl, rr, rx, rh) ->
            if lh > rh + balanceTolerance then
                AvlTree.Balance (comparer, ll, AvlTree.Join comparer root lr r, lx)
            else if rh > lh + balanceTolerance then
                AvlTree.Balance (comparer, AvlTree.Join comparer root l rl, rr, rx)
            else
                AvlTree.Create (root, l, r)

    /// Reroot of balanced trees.
    /// Takes two trees representing disjoint sets and combines them, returning
    /// a new balanced tree representing the union of the two sets.
    static member Reroot comparer l (r : AvlTree<'T>) =
        match l, r with
        | Empty, Empty ->
            Empty
        | set, Empty
        | Empty, set ->
            set
        | Node (_,_,_,lh), Node (_,_,_,rh) ->
            if lh > rh then
                let root, l' = AvlTree.ExtractMax l
                AvlTree.Join comparer root l' r
            else
                let root, r' = AvlTree.ExtractMin r
                AvlTree.Join comparer root l r'


/// A Discrete Interval Encoding Tree (DIET) specialized to the 'char' type.
/// This is abbreviated in our documentation as a 'char-DIET'.
type private CharDiet = AvlTree<char * char>

/// Functional operations for char-DIETs.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private CharDiet =
    open System.Collections.Generic
    open LanguagePrimitives

    (* TODO :   Perhaps define a function, 'adjacent', which determines if
                two points are adjacent via the 'dist' function. It should check if
                the distance is 1 or -1.
                Instead of using 'pred' and 'succ', we could define 'isPred' and 'isSucc'
                functions which also use the 'dist' function. If it's feasible to modify
                the algorithm to use these instead, then we'd only need the type to provide
                the 'dist' function -- we could derive all of the other operations from it. *)

    /// Character interval comparer.
    let private comparer =
        LanguagePrimitives.FastGenericComparer<char * char>

    /// Returns the predecessor of the given value.
    let inline private pred (c : char) : char =
        char (int c - 1)
    
    /// Returns the successor of the given value.
    let inline private succ (c : char) : char =
        char (int c + 1)

    /// Returns the distance between two values -- in other words,
    /// the number of distinct values within the interval defined
    /// by the specified endpoints.
    let inline private dist (x : char) (y : char) : int =
        int y - int x

    /// Similar to 'pred', but clamps the value to a specified lower limit.
    let inline private clampedPred (lowerBound : char) (c : char) =
        if lowerBound < c then
            char (int c - 1)
        else c

//    /// Similar to 'succ', but clamps the value to a specified upper limit.
//    let inline private clampedSucc (upperBound : char) (c : char) =
//        if upperBound > c then
//            char (int c + 1)
//        else c

    //
    let rec private find_del_left p (tree : CharDiet) =
        match tree with
        | Empty ->
            p, Empty
        | Node (left, right, (x, y), _) ->
            if p > succ y then
                let p', right' = find_del_left p right
                p', AvlTree.Join comparer (x, y) left right'
            elif p < x then
                find_del_left p left
            else
                x, left

    //
    let rec private find_del_right p (tree : CharDiet) =
        match tree with
        | Empty ->
            p, Empty
        | Node (left, right, (x, y), _) ->
            if p < pred x then
                let p', left' = find_del_right p left
                p', AvlTree.Join comparer (x, y) left' right
            elif p > y then
                find_del_right p right
            else
                y, right

    /// An empty DIET.
    let empty : CharDiet =
        AvlTree.Empty

    /// Determines if a DIET is empty.
    let inline isEmpty (tree : CharDiet) =
        AvlTree.IsEmptyTree tree

    /// Determines if a DIET contains a specified value.
    let rec contains value (tree : CharDiet) =
        match tree with
        | Empty ->
            false
        | Node (left, right, (x, y), _) ->
            if value < x then
                contains value left
            elif value > y then
                contains value right
            else true
        
    /// Gets the maximum (greatest) value stored in the DIET.
    let maxElement (tree : CharDiet) : char =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | tree ->
            snd <| AvlTree.MaxElement tree
    
    /// Gets the minimum (least) value stored in the DIET.
    let minElement (tree : CharDiet) : char =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | tree ->
            fst <| AvlTree.MinElement tree

    /// Gets the minimum (least) and maximum (greatest) values store in the DIET.
    let bounds (tree : CharDiet) : char * char =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | tree ->
            minElement tree, maxElement tree

    /// Creates a DIET containing the specified value.
    let singleton value : CharDiet =
        AvlTree.Singleton (value, value)

    /// Creates a DIET containing the specified range of values.
    let ofRange minValue maxValue : CharDiet =
        // For compatibility with the F# range operator,
        // when minValue > minValue it's just considered
        // to be an empty range.
        if minValue >= maxValue then
            empty
        else
            AvlTree.Singleton (minValue, maxValue)

    /// Returns the number of elements in the set.
    let count (t : CharDiet) =
        // OPTIMIZE : Modify this to use a mutable stack instead of an F# list.
        let rec cardinal_aux acc = function
            | [] -> acc
            | Empty :: ts ->
                cardinal_aux acc ts
            | Node (left, right, (x, y), _) :: ts ->
                let d = dist x y
                cardinal_aux (acc + d + 1) (left :: right :: ts)
        
        cardinal_aux 0 [t]

    /// Returns the number of intervals in the set.
    let intervalCount (t : CharDiet) =
        // OPTIMIZE : Modify this to use a mutable stack instead of an F# list.
        let rec cardinal_aux acc = function
            | [] -> acc
            | Empty :: ts ->
                cardinal_aux acc ts
            | Node (left, right, _, _) :: ts ->
                cardinal_aux (acc + 1) (left :: right :: ts)
        
        cardinal_aux 0 [t]

    /// Returns a new set with the specified value added to the set.
    /// No exception is thrown if the set already contains the value.
    let rec add value (tree : CharDiet) : CharDiet =
        match tree with
        | Empty ->
            AvlTree.Singleton (value, value)
        | Node (left, right, (x, y), h) ->
            if value >= x then
                if value <= y then
                    // The value is already in [x, y] so the tree
                    // does not need to be modified.
                    tree
                elif value > succ y then
                    // The value is above the interval and is not adjacent
                    // to it, so recurse down the right subtree to add the value
                    // then join the result with the left subtree.
                    AvlTree.Join comparer (x, y) left (add value right)
                else
                    match right with
                    | Empty ->
                        Node (left, Empty, (x, value), h)
                    | _ ->
                        let (u, v), r = AvlTree.ExtractMin right
                        if pred u = value then
                            AvlTree.Join comparer (x, v) left r
                        else
                            Node (left, right, (x, value), h)

            elif value < pred x then
                AvlTree.Join comparer (x, y) (add value left) right
            else
                match left with
                | Empty ->
                    Node (Empty, right, (value, y), h)
                | _ ->
                    let (u, v), l = AvlTree.ExtractMax left
                    if succ v = value then
                        AvlTree.Join comparer (u, y) l right
                    else
                        Node (left, right, (value, y), h)

    /// Returns a new set with the specified range of values added to the set.
    /// No exception is thrown if any of the values are already contained in the set.
    let rec addRange (a, b) (tree : CharDiet) : CharDiet =
        match tree with
        | Empty ->
            AvlTree.Singleton (a, b)
        | Node (left, right, (x, y), _) ->
            if b < pred x then
                AvlTree.Join comparer (x, y) (addRange (a, b) left) right
            elif a > succ y then
                AvlTree.Join comparer (x, y) left (addRange (a, b) right)
            else
                // Now, we know the interval (a, b) being inserted either overlaps or is
                // adjancent to the current inverval (x, y), so we merge them.
                let x', left' =
                    if a >= x then x, left
                    else find_del_left a left
                let y', right' =
                    if b <= y then y, right
                    else find_del_right b right

                AvlTree.Join comparer (x', y') left' right'

    /// Returns a new set with the given element removed.
    /// No exception is thrown if the set doesn't contain the specified element.
    let rec remove value (tree : CharDiet) : CharDiet =
        match tree with
        | Empty ->
            Empty
        | Node (left, right, (x, y), h) ->
            let czx = compare value x
            if czx < 0 then
                // value < x, so recurse down the left subtree.
                AvlTree.Join comparer (x, y) (remove value left) right
            else
                let cyz = compare y value
                if cyz < 0 then
                    // y < value, so recurse down the right subtree.
                    AvlTree.Join comparer (x, y) left (remove value right)
                elif cyz = 0 then
                    if czx = 0 then
                        AvlTree.Reroot comparer left right
                    else
                        Node (left, right, (x, pred y), h)
                elif czx = 0 then
                    Node (left, right, (succ x, y), h)
                else
                    addRange (succ value, y) (Node (left, right, (x, pred value), h))

    /// Determines if a value is greater than or equal to a given
    /// limit value if one is specified.
    let greater_limit limit value =
        match limit with
        | None -> false
        | Some limit ->
            value >= limit

    /// Helper function for computing the union of two sets.
    let rec private union' (input : CharDiet) limit head (stream : CharDiet)
        : CharDiet * (char * char) option * CharDiet =
        match head, input with
        | None, _ ->
            input, None, Empty
        | _, Empty ->
            Empty, head, stream
        | Some (x, y), Node (left, right, (a, b), _) ->
            let left', head, stream =
                if x < a then
                    union' left (Some <| pred a) head stream
                else
                    left, head, stream
            union_helper left' (a, b) right limit head stream

    /// Helper function for computing the union of two sets.
    and private union_helper left (a, b) (right : CharDiet) limit head stream =
        match head with
        | None ->
            AvlTree.Join comparer (a, b) left right, None, Empty
        | Some (x, y) ->
            if y < a && y < pred a then
                let left' = addRange (x, y) left
                AvlTree.TryExtractMin stream
                ||> union_helper left' (a, b) right limit

            elif x > b && x > succ b then
                let right', head, stream = union' right limit head stream
                AvlTree.Join comparer (a, b) left right', head, stream

            elif b >= y then
                AvlTree.TryExtractMin stream
                ||> union_helper left (min a x, b) right limit

            elif greater_limit limit y then
                left, Some (min a x, y), stream

            else
                let right', head, stream = union' right limit (Some (min a x, y)) stream
                AvlTree.Reroot comparer left right', head, stream

    /// Computes the union of the two sets.
    let rec union (input : CharDiet) (stream : CharDiet) : CharDiet =
        if AvlTree.Height stream > AvlTree.Height input then
            union stream input
        else
            #if DEBUG
            let inputCount = count input
            let streamCount = count stream
            /// The minimum possible number of elements in the resulting set.
            let minPossibleResultCount =
                max inputCount streamCount
            /// The maximum possible number of elements in the resulting set.
            let maxPossibleResultCount =
                inputCount + streamCount
            #endif

            // TEMP : This is a naive implementation of the union operation --
            // we only use it here to help track down the bug in the union operation
            // and to test that the rest of the code works correctly.
            let result = AvlTree.FoldBack addRange stream input

//            let result =
//                let result, head', stream'' =
//                    AvlTree.TryExtractMin stream
//                    ||> union' input None
//
//                match head' with
//                | None ->
//                    result
//                | Some i ->
//                    AvlTree.Join comparer i result stream''

            #if DEBUG
            let resultCount = count result
//            let inputArr =
//                if resultCount >= minPossibleResultCount then Array.empty
//                else toArray input
//            let streamArr =
//                if resultCount >= minPossibleResultCount then Array.empty
//                else toArray stream
                    
            Debug.Assert (
                resultCount >= minPossibleResultCount,
                sprintf "The result set should not contain fewer than %i elements, but it contains only %i elements."
                    minPossibleResultCount resultCount)
            Debug.Assert (
                resultCount <= maxPossibleResultCount,
                sprintf "The result set should not contain more than %i elements, but it contains %i elements."
                    maxPossibleResultCount resultCount)
            #endif
            result

    /// Helper function for computing the intersection of two sets.
    let rec private inter' (input : CharDiet) head (stream : CharDiet) : CharDiet * (char * char) option * CharDiet =
        match head, input with
        | None, _ ->
            Empty, None, Empty
        | _, Empty ->
            Empty, head, stream
        | Some (x, y), Node (left, right, (a, b), _) ->
            let left, head, stream =
                if x < a then
                    inter' left head stream
                else
                    Empty, head, stream

            inter_helper (a, b) right left head stream

    /// Helper function for computing the intersection of two sets.
    and private inter_helper (a, b) (right : CharDiet) (left : CharDiet) head stream =
        match head with
        | None ->
            left, None, Empty
        | Some (x, y) ->
            if y < a then
                match stream with
                | Empty ->
                    left, None, Empty
                | _ ->
                    let head, stream = AvlTree.ExtractMin stream
                    inter_helper (a, b) right left (Some head) stream
            elif b < x then
                let right, head, stream = inter' right head stream
                AvlTree.Reroot comparer left right, head, stream
            elif y >= clampedPred y b then
                let right, head, stream = inter' right head stream
                let right' = AvlTree.Join comparer (max x a, min y b) left right
                right', head, stream
            else
                let left = addRange (max x a, y) left
                inter_helper (succ y, b) right left head stream

    /// Computes the intersection of the two sets.
    let rec intersect (input : CharDiet) (stream : CharDiet) : CharDiet =
        if AvlTree.Height stream > AvlTree.Height input then
            intersect stream input
        else
        match stream with
        | Empty -> Empty
        | _ ->
            #if DEBUG
            let inputCount = count input
            let streamCount = count stream
            /// The minimum possible number of elements in the resulting set.
            let minPossibleResultCount =
                min inputCount streamCount
            /// The maximum possible number of elements in the resulting set.
            let maxPossibleResultCount =
                inputCount + streamCount
            #endif

            let result, _, _ =
                let head, stream = AvlTree.ExtractMin stream
                inter' input (Some head) stream

            #if DEBUG
            let resultCount = count result
//            let inputArr =
//                if resultCount >= minPossibleResultCount then Array.empty
//                else toArray input
//            let streamArr =
//                if resultCount >= minPossibleResultCount then Array.empty
//                else toArray stream
                    
            Debug.Assert (
                resultCount >= minPossibleResultCount,
                sprintf "The result set should not contain fewer than %i elements, but it contains only %i elements."
                    minPossibleResultCount resultCount)
            Debug.Assert (
                resultCount <= maxPossibleResultCount,
                sprintf "The result set should not contain more than %i elements, but it contains %i elements."
                    maxPossibleResultCount resultCount)
            #endif
            result

    /// Helper function for computing the difference of two sets.
    let rec private diff' (input : CharDiet) head (stream : CharDiet) : CharDiet * (char * char) option * CharDiet =
        match head, input with
        | None, _->
            input, None, Empty
        | _, Empty ->
            Empty, head, stream
        | Some (x, y), Node (left, right, (a, b), _) ->
            let left, head, stream =
                if x < a then
                    diff' left head stream
                else
                    left, head, stream
            diff_helper (a, b) right left head stream

    /// Helper function for computing the difference of two sets.
    and private diff_helper (a, b) (right : CharDiet) (left : CharDiet) head stream =
        match head with
        | None ->
            AvlTree.Join comparer (a, b) left right, None, Empty
        | Some (x, y) ->
            if y < a then
                // [x, y] and [a, b] are disjoint
                let head, stream = AvlTree.TryExtractMin stream
                diff_helper (a, b) right left head stream
            elif b < x then
                // [a, b] and [x, y] are disjoint
                let right, head, stream = diff' right head stream
                AvlTree.Join comparer (a, b) left right, head, stream
            elif a < x then
                // [a, b] and [x, y] overlap
                // a < x
                diff_helper (x, b) right ((addRange (a, pred x) left)) head stream
            elif y < b then
                // [a, b] and [x, y] overlap
                // y < b
                let head, stream = AvlTree.TryExtractMin stream
                diff_helper (succ y, b) right left head stream
            else
                // [a, b] and [x, y] overlap
                let right, head, stream = diff' right head stream
                AvlTree.Reroot comparer left right, head, stream

    /// Returns a new set with the elements of the second set removed from the first.
    let difference (input : CharDiet) (stream : CharDiet) : CharDiet =
        match stream with
        | Empty -> input
        | _ ->
            #if DEBUG
            /// The maximum possible number of elements in the resulting set.
            let maxPossibleResultCount = count input
            #endif

            let result, _, _ =
                AvlTree.TryExtractMin stream    
                ||> diff' input

            #if DEBUG
            let resultCount = count result
            Debug.Assert (
                resultCount <= maxPossibleResultCount,
                sprintf "The result set should not contain more than %i elements, but it contains %i elements."
                    maxPossibleResultCount resultCount)
            #endif
            result

    /// Comparison function for DIETs.
    let rec comparison (t1 : CharDiet) (t2 : CharDiet) =
        match t1, t2 with
        | Node (_,_,_,_), Empty -> 1
        | Empty, Empty -> 0
        | Empty, Node (_,_,_,_) -> -1
        | Node (_,_,_,_), Node (_,_,_,_) ->
            let (ix1, iy1), r1 = AvlTree.ExtractMin t1
            let (ix2, iy2), r2 = AvlTree.ExtractMin t2
            let c =
                let d = compare ix1 ix2
                if d <> 0 then -d
                else compare iy1 iy2
            if c <> 0 then c
            else comparison r1 r2

    /// Equality function for DIETs.
    let equal (t1 : CharDiet) (t2 : CharDiet) =
        comparison t1 t2 = 0

    /// Applies the given accumulating function to all elements in a DIET.
    let fold (folder : 'State -> char -> 'State) (state : 'State) (tree : CharDiet) =
        // Preconditions
        // NONE -- Skip null check because the Empty tree is represented as null.

        let folder = FSharpFunc<_,_,_>.Adapt folder

        let rangeFolder (state : 'State) (lo, hi) =
            // Fold over the items in increasing order.
            let mutable state = state
            for x = int lo to int hi do
                state <- folder.Invoke (state, char x)
            state

        AvlTree.Fold rangeFolder state tree

    /// Applies the given accumulating function to all elements in a DIET.
    let foldBack (folder : char -> 'State -> 'State) (tree : CharDiet) (state : 'State) =
        // Preconditions
        // NONE -- Skip null check because the Empty tree is represented as null.

        let folder = FSharpFunc<_,_,_>.Adapt folder

        let rangeFolder (lo, hi) (state : 'State) =
            // Fold over the items in decreasing order.
            let mutable state = state
            for x = int hi downto int lo do
                state <- folder.Invoke (char x, state)
            state

        AvlTree.FoldBack rangeFolder state tree

    /// Applies the given function to all elements in a DIET.
    let iter (action : char -> unit) (tree : CharDiet) =
        // Preconditions
        // NONE -- Skip null check because the Empty tree is represented as null.

        /// Applies the action to all values within an interval.
        let intervalApplicator (lo, hi) =
            for x = int lo to int hi do
                action (char x)

        AvlTree.Iter intervalApplicator tree

    //
    let forall (predicate : char -> bool) (t : CharDiet) =
        // OPTIMIZE : Rewrite this to short-circuit and return early
        // if we find a non-matching element.
        (true, t)
        ||> fold (fun state el ->
            state && predicate el)

    //
    let exists (predicate : char -> bool) (t : CharDiet) =
        // OPTIMIZE : Rewrite this to short-circuit and return early
        // if we find a non-matching element.
        (false, t)
        ||> fold (fun state el ->
            state || predicate el)

    //
    let rec toSeq (tree : CharDiet) =
        seq {
        match tree with
        | Empty -> ()
        | Node (l, r, (x, y), _) ->
            yield! toSeq l
            yield! seq {x .. y}
            yield! toSeq r
        }

    //
    let toList (tree : CharDiet) =
        ([], tree)
        ||> fold (fun list el ->
            el :: list)

    //
    let toArray (tree : CharDiet) =
        let elements = ResizeArray ()
        iter elements.Add tree
        elements.ToArray ()

    //
    let toSet (tree : CharDiet) =
        (Set.empty, tree)
        ||> fold (fun set el ->
            Set.add el set)

    /// Builds a new DIET from the elements of a sequence.
    let ofSeq (sequence : seq<_>) : CharDiet =
        (Empty, sequence)
        ||> Seq.fold (fun tree el ->
            add el tree)

    /// Builds a new DIET from the elements of an F# list.
    let ofList (list : _ list) : CharDiet =
        (Empty, list)
        ||> List.fold (fun tree el ->
            add el tree)

    /// Builds a new DIET from the elements of an array.
    let ofArray (array : _[]) : CharDiet =
        (Empty, array)
        ||> Array.fold (fun tree el ->
            add el tree)

    /// Builds a new DIET from an F# Set.
    let ofSet (set : Set<_>) : CharDiet =
        (Empty, set)
        ||> Set.fold (fun tree el ->
            add el tree)


/// Character set implementation based on a Discrete Interval Encoding Tree.
/// This is faster and more efficient than the built-in F# Set<'T>,
/// especially for dense sets.
[<DebuggerDisplay("Count = {Count}, Intervals = {IntervalCount}")>]
type CharSet private (tree : CharDiet) =
    //
    static let empty = CharSet (CharDiet.empty)

    //
    static member Empty
        with get () = empty
    
    override __.GetHashCode () =
        // TODO : Come up with a better hashcode function.
        (CharDiet.count tree) * (int <| AvlTree.Height tree)
    
    override __.Equals other =
        match other with
        | :? CharSet as other ->
            CharDiet.equal tree other.Tree
        | _ ->
            false

    //
    member private __.Tree
        with get () = tree

    //
    member __.Count
        with get () =
            CharDiet.count tree

    //
    member __.IntervalCount
        with get () =
            CharDiet.intervalCount tree

    //
    member __.MaxElement
        with get () =
            CharDiet.maxElement tree

    //
    member __.MinElement
        with get () =
            CharDiet.minElement tree

    /// The set containing the given element.
    static member FromElement value : CharSet =
        CharSet (CharDiet.singleton value)

    /// The set containing the elements in the given range.
    static member FromRange (lowerBound, upperBound) : CharSet =
        CharSet (CharDiet.ofRange lowerBound upperBound)

    //
    static member IsEmpty (charSet : CharSet) : bool =
        CharDiet.isEmpty charSet.Tree

    /// Returns a new set with an element added to the set.
    /// No exception is raised if the set already contains the given element.
    static member Add (value, charSet : CharSet) : CharSet =
        CharSet (CharDiet.add value charSet.Tree)

    //
    static member AddRange (lower, upper, charSet : CharSet) : CharSet =
        CharSet (CharDiet.addRange (lower, upper) charSet.Tree)

    //
    static member Remove (value, charSet : CharSet) : CharSet =
        CharSet (CharDiet.remove value charSet.Tree)

    //
    static member Contains (value, charSet : CharSet) : bool =
        CharDiet.contains value charSet.Tree

    //
    static member OfSeq (sequence : seq<char>) : CharSet =
        CharSet (CharDiet.ofSeq sequence)

    //
    static member OfList (list : char list) : CharSet =
        CharSet (CharDiet.ofList list)

    //
    static member OfArray (array : char[]) : CharSet =
        CharSet (CharDiet.ofArray array)

    //
    static member OfSet (set : Set<char>) : CharSet =
        CharSet (CharDiet.ofSet set)

    //
    static member ToSeq (charSet : CharSet) : seq<char> =
        CharDiet.toSeq charSet.Tree

    //
    static member ToList (charSet : CharSet) : char list =
        CharDiet.toList charSet.Tree

    //
    static member ToArray (charSet : CharSet) : char[] =
        CharDiet.toArray charSet.Tree

    //
    static member ToSet (charSet : CharSet) : Set<char> =
        CharDiet.toSet charSet.Tree

    //
    static member Difference (charSet1 : CharSet, charSet2 : CharSet) : CharSet =
        CharSet (CharDiet.difference charSet1.Tree charSet2.Tree)

    //
    static member Intersect (charSet1 : CharSet, charSet2 : CharSet) : CharSet =
        CharSet (CharDiet.intersect charSet1.Tree charSet2.Tree)

    //
    static member Union (charSet1 : CharSet, charSet2 : CharSet) : CharSet =
        CharSet (CharDiet.union charSet1.Tree charSet2.Tree)

    //
    static member Exists (predicate, charSet : CharSet) : bool =
        CharDiet.exists predicate charSet.Tree

    //
    static member Forall (predicate, charSet : CharSet) : bool =
        CharDiet.forall predicate charSet.Tree

    //
    static member Fold (folder : 'State -> _ -> 'State, state, charSet : CharSet) : 'State =
        CharDiet.fold folder state charSet.Tree

    //
    static member FoldBack (folder : _ -> 'State -> 'State, state, charSet : CharSet) : 'State =
        CharDiet.foldBack folder charSet.Tree state

    //
    static member Iter (action, charSet : CharSet) : unit =
        CharDiet.iter action charSet.Tree

    //
    static member IterIntervals (action, charSet : CharSet) : unit =
        let action = FSharpFunc<_,_,_>.Adapt action
        charSet.Tree |> AvlTree.Iter action.Invoke

    //
    static member Map (mapping : char -> char, charSet : CharSet) : CharSet =
        notImpl "CharSet.Map"

    //
    static member Filter (predicate : char -> bool, charSet : CharSet) : CharSet =
        notImpl "CharSet.Filter"

    //
    static member Partition (predicate : char -> bool, charSet : CharSet) : CharSet * CharSet =
        notImpl "CharSet.Partition"

    interface System.IComparable with
        member this.CompareTo other =
            match other with
            | :? CharSet as other ->
                CharDiet.comparison this.Tree other.Tree
            | _ ->
                invalidArg "other" "The argument is not an instance of CharSet."

    interface System.IComparable<CharSet> with
        member this.CompareTo other =
            CharDiet.comparison tree other.Tree

    interface System.IEquatable<CharSet> with
        member this.Equals other =
            CharDiet.equal tree other.Tree


/// Functional programming operators related to the CharSet type.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module CharSet =
    /// The empty set.
    [<CompiledName("Empty")>]
    let empty = CharSet.Empty

    /// Returns 'true' if the set is empty.
    [<CompiledName("IsEmpty")>]
    let inline isEmpty charSet =
        CharSet.IsEmpty charSet

    /// Returns the number of elements in the set.
    [<CompiledName("Count")>]
    let inline count (charset : CharSet) =
        charset.Count

    /// Returns the number of intervals in the set.
    [<CompiledName("IntervalCount")>]
    let inline intervalCount (charset : CharSet) =
        charset.IntervalCount

    /// Returns the highest (greatest) value in the set.
    [<CompiledName("MaxElement")>]
    let inline maxElement (charSet : CharSet) =
        charSet.MaxElement

    /// Returns the lowest (least) value in the set.
    [<CompiledName("MinElement")>]
    let inline minElement (charSet : CharSet) =
        charSet.MinElement

    /// The set containing the given element.
    [<CompiledName("Singleton")>]
    let inline singleton c =
        CharSet.FromElement c

    /// Evaluates to 'true' if the given element is in the given set.
    [<CompiledName("Contains")>]
    let inline contains value charSet =
        CharSet.Contains (value, charSet)

    /// Returns a new set with an element added to the set.
    /// No exception is raised if the set already contains the given element.
    [<CompiledName("Add")>]
    let inline add value charSet =
        CharSet.Add (value, charSet)

    /// Returns a new set with a range of elements added to the set.
    /// No exception is raised if the set already contains any of the elements.
    [<CompiledName("AddRange")>]
    let inline addRange lower upper charSet =
        CharSet.AddRange (lower, upper, charSet)

    /// Returns a new set with the given element removed.
    /// No exception is raised if the set doesn't contain the given element.
    [<CompiledName("Remove")>]
    let inline remove value charSet =
        CharSet.Remove (value, charSet)

    /// Tests if any element of the collection satisfies the given predicate.
    /// If the input function is <c>predicate</c> and the elements are <c>i0...iN</c>,
    /// then this function computes predicate <c>i0 or ... or predicate iN</c>.
    [<CompiledName("Exists")>]
    let inline exists (predicate : char -> bool) charSet =
        CharSet.Exists (predicate, charSet)

    /// Tests if all elements of the collection satisfy the given predicate.
    /// If the input function is <c>p</c> and the elements are <c>i0...iN</c>,
    /// then this function computes <c>p i0 && ... && p iN</c>.
    [<CompiledName("Forall")>]
    let inline forall (predicate : char -> bool) charSet =
        CharSet.Forall (predicate, charSet)

    /// Applies the given function to each element of the set, in order from least to greatest.
    [<CompiledName("Iter")>]
    let inline iter (action : char -> unit) charSet =
        CharSet.Iter (action, charSet)

    /// Applies the given function to each element of the set, in order from least to greatest.
    [<CompiledName("IterIntervals")>]
    let inline iterIntervals action charSet =
        CharSet.IterIntervals (action, charSet)
    
    /// Applies the given accumulating function to all the elements of the set.
    [<CompiledName("Fold")>]
    let inline fold (folder : 'State -> char -> 'State) (state : 'State) charSet =
        CharSet.Fold (folder, state, charSet)

    /// Applies the given accumulating function to all the elements of the set.
    [<CompiledName("FoldBack")>]
    let inline foldBack (folder : char -> 'State -> 'State) charSet (state : 'State) =
        CharSet.FoldBack (folder, state, charSet)

    /// Returns a new set containing the results of applying the given function to each element of the input set.
    [<CompiledName("Map")>]
    let map (mapping : char -> char) charSet =
        CharSet.Map (mapping, charSet)

    /// Returns a new set containing only the elements of the collection for which the given predicate returns true.
    [<CompiledName("Filter")>]
    let inline filter (predicate : char -> bool) charSet =
        CharSet.Filter (predicate, charSet)

    /// The set containing the elements in the given range.
    [<CompiledName("OfRange")>]
    let inline ofRange lowerBound upperBound =
        CharSet.FromRange (lowerBound, upperBound)

    /// Creates a new set from the given enumerable object.
    [<CompiledName("OfSeq")>]
    let inline ofSeq seq =
        CharSet.OfSeq seq

    /// Creates a set that contains the same elements as the given list.
    [<CompiledName("OfList")>]
    let inline ofList list =
        CharSet.OfList list

    /// Creates a set that contains the same elements as the given array.
    [<CompiledName("OfArray")>]
    let inline ofArray array =
        CharSet.OfArray array

    /// Creates a CharSet that contains the same elements as the given Set.
    [<CompiledName("OfSet")>]
    let inline ofSet set =
        CharSet.OfSet set

    /// Returns an ordered view of the set as an enumerable object.
    [<CompiledName("ToSeq")>]
    let inline toSeq charSet =
        CharSet.ToSeq charSet

    /// Creates a list that contains the elements of the set in order.
    [<CompiledName("ToList")>]
    let inline toList charSet =
        CharSet.ToList charSet

    /// Creates an array that contains the elements of the set in order.
    [<CompiledName("ToArray")>]
    let inline toArray charSet =
        CharSet.ToArray

    /// Creates a Set that contains the same elements as the given CharSet.
    [<CompiledName("ToSet")>]
    let inline toSet charSet =
        CharSet.ToSet charSet

    /// Returns a new set with the elements of the second set removed from the first.
    [<CompiledName("Difference")>]
    let inline difference set1 set2 =
        CharSet.Difference (set1, set2)

    /// Computes the intersection of the two sets.
    [<CompiledName("Intersect")>]
    let inline intersect set1 set2 =
        CharSet.Intersect (set1, set2)

    /// Computes the union of the two sets.
    [<CompiledName("Union")>]
    let inline union set1 set2 =
        CharSet.Union (set1, set2)

    /// Splits the set into two sets containing the elements for which
    /// the given predicate returns true and false respectively.
    [<CompiledName("Partition")>]
    let inline partition predicate charSet =
        CharSet.Partition (predicate, charSet)

