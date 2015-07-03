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


[<AutoOpen>]
module private Constants =
    /// AVL balance tolerance factor.
    let [<Literal>] balanceTolerance = 2u


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
#if DEBUG
[<StructuredFormatDisplay("{DisplayFormatted}")>]
#else
[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
#endif
[<NoEquality; NoComparison>]
[<DebuggerTypeProxy(typedefof<AvlTreeDebuggerProxy<int>>)>]
type AvlTree<'T when 'T : comparison> =
    /// Empty tree.
    | Empty
    /// Node.
    // Left-Child, Right-Child, Value, Height
    | Node of AvlTree<'T> * AvlTree<'T> * 'T * uint32

    //
    static member private CompareStacks (comparer : IComparer<'T>, l1 : AvlTree<'T> list, l2 : AvlTree<'T> list) : int =
        // OPTIMIZATION : If the lists are identical, there's no need to compare them.
        if l1 == l2 then 0 else

        match l1, l2 with
        | [], [] -> 0
        | [], _ -> -1
        | _, [] -> 1

        // OPTIMIZATION : If the trees are identical, there's no need to compare them.
        | t1 :: l1, t2 :: l2
            when t1 == t2 ->
            AvlTree.CompareStacks (comparer, l1, l2)

        | Empty :: t1, Empty :: t2 ->
            AvlTree.CompareStacks (comparer, t1, t2)

        | Node (Empty, Empty, n1k, _) :: t1, Node (Empty, Empty, n2k, _) :: t2 ->
            match comparer.Compare (n1k, n2k) with
            | 0 ->
                AvlTree.CompareStacks (comparer, t1, t2)
            | c -> c

        | Node (Empty, Empty, n1k, _) :: t1, Node (Empty, n2r, n2k, _) :: t2 ->
            match comparer.Compare (n1k, n2k) with
            | 0 ->
                AvlTree.CompareStacks (comparer, Empty :: t1, n2r :: t2)
            | c -> c

        | Node (Empty, n1r, n1k, _) :: t1, Node (Empty, Empty, n2k, _) :: t2 ->
            match comparer.Compare (n1k, n2k) with
            | 0 ->
                AvlTree.CompareStacks (comparer, n1r :: t1, Empty :: t2)
            | c -> c

        | Node (Empty, n1r, n1k, _) :: t1, Node (Empty, n2r, n2k, _) :: t2 ->
            match comparer.Compare (n1k, n2k) with
            | 0 ->
                AvlTree.CompareStacks (comparer, n1r :: t1, n2r :: t2)
            | c -> c

        | Node (Empty, Empty, _, _) :: _, _ ->
            AvlTree.CompareStacks (comparer, Empty :: l1, l2)
        
        | Node (n1l, n1r, n1k, _) :: t1, _ ->
            AvlTree.CompareStacks (comparer, n1l :: Node (Empty, n1r, n1k, 0u) :: t1, l2)
        
        | _, Node (Empty, Empty, _, _) :: _ ->
            AvlTree.CompareStacks (comparer, l1, Empty :: l2)
        
        | _, Node (n2l, n2r, n2k, _) :: t2 ->
            AvlTree.CompareStacks (comparer, l1, n2l :: Node (Empty, n2r, n2k, 0u) :: t2)
                
    //
    static member Compare (comparer : IComparer<'T>, s1 : AvlTree<'T>, s2 : AvlTree<'T>) : int =
        // OPTIMIZATION : If the trees are identical, there's no need to compare them.
        if s1 == s2 then 0
        else
            match s1, s2 with
            | Empty, Empty -> 0
            | Empty, _ -> -1
            | _, Empty -> 1
            
            // OPTIMIZATION : For this simple, common case, avoid the overhead of creating lists.
            | Node (Empty, Empty, x, _), Node (Empty, Empty, y, _) ->
                compare x y

            | _ ->
                AvlTree<'T>.CompareStacks (comparer, [s1], [s2])

    /// Computes the height of a AvlTree (rather than returning the height value stored in it's root).
    [<Pure>]
    static member private ComputeHeight (tree : AvlTree<'T>) =
        match tree with
        | Empty -> 0u
        | Node (l, r, _, _) ->
            1u + max (AvlTree.ComputeHeight l) (AvlTree.ComputeHeight r)
        
    /// Determines if a AvlTree is correctly formed.
    [<Pure>]
    static member internal AvlInvariant (tree : AvlTree<'T>) =
        match tree with
        | Empty -> true
        | Node (l, r, _, h) ->
            let height_l = AvlTree.ComputeHeight l
            let height_r = AvlTree.ComputeHeight r
            let height_diff = (max height_l height_r) - (min height_l height_r)
            
            height_diff <= balanceTolerance
            && h = ((max height_l height_r) + 1u)
            && AvlTree.AvlInvariant l
            && AvlTree.AvlInvariant r

    /// Returns the height of a AvlTree.
    [<Pure>]
    static member inline Height (tree : AvlTree<'T>) =
        match tree with
        | Empty -> 0u
        | Node (_,_,_,h) -> h

    /// Returns the absolute difference in heights between two AvlTrees.
    [<Pure>]
    static member private HeightDiff (t1, t2 : AvlTree<'T>) =
        (max (AvlTree.Height t1) (AvlTree.Height t2)) - (min (AvlTree.Height t1) (AvlTree.Height t2))

    /// Determines if a AvlTree is empty.
    [<Pure>]
    static member inline IsEmptyTree (tree : AvlTree<'T>) =
        match tree with
        | Empty -> true
        | Node (_,_,_,_) -> false

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

    /// Determines if a AvlTree contains a specified value.
    [<Pure>]
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

    /// Creates a AvlTree whose root node holds the specified value
    /// and the specified left and right subtrees.
    [<Pure>]
    static member inline private Create (l, r : AvlTree<'T>, value) =
        //assert (AvlTree.AvlInvariant l)
        //assert (AvlTree.AvlInvariant r)
        //assert (AvlTree.HeightDiff (l, r) <= balanceTolerance)
        Node (l, r, value, (max (AvlTree.Height l) (AvlTree.Height r)) + 1u)

    /// Creates a AvlTree containing the specified value.
    [<Pure>]
    static member Singleton value : AvlTree<'T> =
        AvlTree.Create (Empty, Empty, value)

    //
    static member private mkt_bal_l (n, l, r : AvlTree<'T>) =
        // Preconditions
        //assert (AvlTree.AvlInvariant l)
        //assert (AvlTree.AvlInvariant r)
        //assert (AvlTree.Height l <= AvlTree.Height r + balanceTolerance)

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
                        AvlTree.Create (
                            AvlTree.Create (ll, lrl, ln),
                            AvlTree.Create (lrr, r, n),
                            lrn)
                else
                    AvlTree.Create (ll, AvlTree.Create (lr, r, n), ln)
        else
            AvlTree.Create (l, r, n)

    //
    static member private mkt_bal_r (n, l, r : AvlTree<'T>) =
        // Preconditions
        //assert (AvlTree.AvlInvariant l)
        //assert (AvlTree.AvlInvariant r)
        //assert (AvlTree.Height r <= AvlTree.Height l + balanceTolerance)

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
                        AvlTree.Create (
                            AvlTree.Create (l, rll, n),
                            AvlTree.Create (rlr, rr, rn),
                            rln)
                else
                    AvlTree.Create (AvlTree.Create (l, rl, n), rr, rn)
        else
            AvlTree.Create (l, r, n)

    /// Removes the minimum (least) value from an AvlTree,
    /// returning the value along with the updated tree.
    static member DeleteMin (tree : AvlTree<'T>) =
        // Preconditions
        //assert (AvlTree.AvlInvariant tree)

        match tree with
        | Empty ->
            invalidArg "tree" "Cannot delete the minimum value from an empty tree."
        | Node (Empty, r, n, _) ->
            n, r
        | Node (l, r, n, _) ->
            let n', l' = AvlTree.DeleteMin l
            n', AvlTree.mkt_bal_r (n, l', r)

    /// Removes the minimum (least) value from a AvlTree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    static member TryDeleteMin (tree : AvlTree<'T>) =
        // Preconditions
        //assert (AvlTree.AvlInvariant tree)

        match tree with
        | Empty ->
            None, tree
        | Node (Empty, r, n, _) ->
            Some n, r
        | tree ->
            let n', l' = AvlTree.DeleteMin tree
            Some n', l'

    /// Removes the maximum (greatest) value from an AvlTree,
    /// returning the value along with the updated tree.
    static member DeleteMax (tree : AvlTree<'T>) =
        // Preconditions
        //assert (AvlTree.AvlInvariant tree)

        match tree with
        | Empty ->
            invalidArg "tree" "Cannot delete the maximum value from an empty tree."
        | Node (l, Empty, n, _) ->
            n, l
        | Node (l, r, n, _) ->
            let n', r' = AvlTree.DeleteMax r
            n', AvlTree.mkt_bal_l (n, l, r')

    /// Removes the maximum (greatest) value from a AvlTree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    static member TryDeleteMax (tree : AvlTree<'T>) =
        // Preconditions
        //assert (AvlTree.AvlInvariant tree)

        match tree with
        | Empty ->
            None, tree
        | Node (l, Empty, n, _) ->
            Some n, l
        | tree ->
            let n', r' = AvlTree.DeleteMax tree
            Some n', r'

    /// Removes the root (median) value from an AvlTree,
    /// returning the value along with the updated tree.
    static member DeleteRoot (tree : AvlTree<'T>) =
        // Preconditions
        //assert (AvlTree.AvlInvariant tree)

        match tree with
        | Empty ->
            invalidArg "tree" "Cannot delete the root of an empty tree."
        | Node (Empty, r, _, _) -> r
        | Node (l, Empty, _, _) -> l
        | Node (l, r, _, _) ->
            let root, l' = AvlTree.DeleteMax l
            AvlTree.mkt_bal_r (root, l', r)

    /// Removes the specified value from the tree.
    /// If the tree doesn't contain the value, no exception is thrown;
    /// the tree will be returned without modification.
    static member Delete (comparer : IComparer<'T>, tree : AvlTree<'T>, value : 'T) =
        // Preconditions
        //assert (AvlTree.AvlInvariant tree)

        match tree with
        | Empty ->
            Empty
        | Node (l, r, n, _) ->
            let comparison = comparer.Compare (value, n)
            if comparison = 0 then
                // x = n
                AvlTree.DeleteRoot tree
            elif comparison < 0 then
                // x < n
                let l' = AvlTree.Delete (comparer, l, value)

                // Only rebalance the tree if an element was actually deleted.
                if l' == l then tree
                else AvlTree.mkt_bal_r (n, l', r)
            else
                // x > n
                let r' = AvlTree.Delete (comparer, r, value)
                
                // Only rebalance the tree if an element was actually deleted.
                if r' == r then tree
                else AvlTree.mkt_bal_l (n, l, r')

    /// Adds a value to a AvlTree.
    /// If the tree already contains the value, no exception is thrown;
    /// the tree will be returned without modification.
    static member Insert (comparer : IComparer<'T>, tree : AvlTree<'T>, value : 'T) =
        // Preconditions
        //assert (AvlTree.AvlInvariant tree)

        match tree with
        | Empty ->
            Node (Empty, Empty, value, 1u)
        | Node (l, r, n, _) ->
            let comparison = comparer.Compare (value, n)
            if comparison = 0 then
                // x = n
                tree
            elif comparison < 0 then
                // x < n
                let l' = AvlTree.Insert (comparer, l, value)

                // Only rebalance the tree if an element was actually inserted.
                if l' == l then tree
                else AvlTree.mkt_bal_l (n, l', r)
            else
                // x > n
                let r' = AvlTree.Insert (comparer, r, value)
                
                // Only rebalance the tree if an element was actually inserted.
                if r' == r then tree
                else AvlTree.mkt_bal_r (n, l, r')

    /// Counts the number of elements in the tree.
    static member Count (tree : AvlTree<'T>) =
        match tree with
        | Empty -> 0u
        | Node (l, r, _, _) ->
            // Count the number of children in the left and right subtrees.
            // Add one to their sum to account for this node.
            1u + (AvlTree.Count l) + (AvlTree.Count r)

    //
    static member Iter (action : 'T -> unit) (tree : AvlTree<'T>) : unit =
        match tree with
        | Empty -> ()
        | Node (l, r, x, _) ->
            // Iterate over the left subtree.
            AvlTree.Iter action l

            // Invoke the action on the current element.
            action x

            // Iterate over the right subtree.
            AvlTree.Iter action r

    /// Applies the given accumulating function to all elements in a AvlTree.
    static member Fold (folder : 'State -> 'T -> 'State) (state : 'State) (tree : AvlTree<'T>) =
        match tree with
        | Empty -> state
        | Node (l, r, x, _) ->
            // Fold over the left subtree.
            let state = AvlTree.Fold folder state l

            // Apply the folder function to the current element.
            let state = folder state x

            // Fold over the right subtree
            AvlTree.Fold folder state r

    /// Applies the given accumulating function to all elements in a AvlTree.
    static member FoldBack (folder : 'T -> 'State -> 'State) (state : 'State) (tree : AvlTree<'T>) =
        match tree with
        | Empty -> state
        | Node (l, r, x, _) ->
            // Fold over the right subtree.
            let state = AvlTree.FoldBack folder state r

            // Apply the folder function to the current element.
            let state = folder x state

            // Fold over the left subtree.
            AvlTree.FoldBack folder state l

    /// Tests if any element of the collection satisfies the given predicate.
    static member Exists (predicate : 'T -> bool) (tree : AvlTree<'T>) : bool =
        match tree with
        | Empty -> false
        | Node (l, r, x, _) ->
            // Try to find a matching element in the left subtree.
            AvlTree.Exists predicate l
            // Does the current element match the predicate?
            || predicate x
            // Try to find a matching element in the right subtree.
            || AvlTree.Exists predicate r

    /// Tests if all elements of the collection satisfy the given predicate.
    static member Forall (predicate : 'T -> bool) (tree : AvlTree<'T>) : bool =
        match tree with
        | Empty -> true
        | Node (l, r, x, _) ->
            // Try to find a non-matching element in the left subtree.
            AvlTree.Forall predicate l
            // Does the current element match the predicate?
            && predicate x
            // Try to find a non-matching element in the right subtree.
            && AvlTree.Forall predicate r

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
    static member private Balance (l, r, n) : AvlTree<'T> =
        // Preconditions
        //assert (AvlTree.AvlInvariant l)
        //assert (AvlTree.AvlInvariant r)
        //assert (AvlTree.HeightDiff (l, r) <= (balanceTolerance + 1u))
        // TODO : Assert all values in 'l' are less than all values in 'r', and also less than 'n'.
        //        Assert 'n' is less than all values in 'r'.

        let lh = AvlTree.Height l
        let rh = AvlTree.Height r
        if lh >= rh + balanceTolerance then // left is heavier than right
            match l with
            | Empty ->
                failwith "Balance"
            | Node (ll, lr, ln, _) ->
                // one of the nodes must have height > height r + 1
                if AvlTree.Height ll >= AvlTree.Height lr then
                    AvlTree.Create (
                        ll,
                        AvlTree.Create (lr, r, n),
                        ln)
                else
                    // balance right: combination
                    match lr with
                    | Empty ->
                        failwith "Balance"
                    | Node (lrl, lrr, lrn, _) ->
                        AvlTree.Create (
                            AvlTree.Create (ll, lrl, ln),
                            AvlTree.Create (lrr, r, n),
                            lrn)
                    
        elif rh >= lh + balanceTolerance then // right is heavier than left
            match r with
            | Empty ->
                failwith "Balance"
            | Node (rl, rr, rn, _) ->
                // one of the nodes must have height > height t1 + 1
                if AvlTree.Height rr >= AvlTree.Height rl then
                    // rotate left
                    AvlTree.Create (
                        AvlTree.Create (l, rl, n),
                        rr,
                        rn)
                else
                    // balance left: combination
                    match rl with
                    | Empty ->
                        failwith "Balance"
                    | Node (rll, rlr, rln, _) ->
                        AvlTree.Create (
                            AvlTree.Create (l, rll, n),
                            AvlTree.Create (rlr, rr, rn),
                            rln)
        else
            AvlTree.Create (l, r, n)

    /// Join two trees together with the specified root element.
    /// Takes two trees representing disjoint sets and combines them, returning
    /// a new balanced tree representing the union of the two sets and the given root element.
    /// This is essentially a recursive version of Balance which can handle
    /// any difference in height between the trees.
    static member Join (comparer, l, r : AvlTree<'T>, root) : AvlTree<'T> =
        // Preconditions
        //assert (AvlTree.AvlInvariant l)
        //assert (AvlTree.AvlInvariant r)
        // TODO : Assert all values in 'l' are less than all values in 'r'.

        match l, r with
        | Empty, Empty ->
            AvlTree.Singleton root
        | Empty, _ ->
            AvlTree.Insert (comparer, r, root)
        | _, Empty ->
            AvlTree.Insert (comparer, l, root)
        | Node (ll, lr, ln, lh), Node (rl, rr, rn, rh) ->
            if lh > rh + balanceTolerance then
                let r' = AvlTree.Join (comparer, lr, r, root)
                AvlTree.Balance (ll, r', ln)
            elif rh > lh + balanceTolerance then
                let l' = AvlTree.Join (comparer, l, rl, root)
                AvlTree.Balance (l', rr, rn)
            else
                //AvlTree.Create (root, l, r)
                AvlTree.Balance (l, r, root)

    /// Reroot of balanced trees.
    /// Takes two trees representing disjoint sets and combines them, returning
    /// a new balanced tree representing the union of the two sets.
    static member Reroot (comparer, l, r : AvlTree<'T>) : AvlTree<'T> =
        // Preconditions
        //assert (AvlTree.AvlInvariant l)
        //assert (AvlTree.AvlInvariant r)
        // TODO : Assert all values in 'l' are less than all values in 'r'.

        match l, r with
        | Empty, Empty ->
            Empty
        | set, Empty
        | Empty, set ->
            set
        | Node (_,_,_,lh), Node (_,_,_,rh) ->
            if lh > rh then
                let root, l' = AvlTree.DeleteMax l
                AvlTree.Join (comparer, l', r, root)
            else
                let root, r' = AvlTree.DeleteMin r
                AvlTree.Join (comparer, l, r', root)

    /// Prints a tree as F# code which, when executed, will re-create the tree.
    static member internal ToCodeString (tree : AvlTree<'T>) : string =
        /// Holds the printed code.
        let sb = System.Text.StringBuilder ()

        // Create an IndentedTextWriter which will write to the StringBuilder.
        using (new IndentedTextWriter (new System.IO.StringWriter (sb), "    ")) <| fun indentedWriter ->
            // Traverse the tree and write the code into the StringBuilder.
            AvlTree.ToCodeStringImpl (tree, indentedWriter)

            // Flush the writer's buffer to make sure everything has been written into
            // the StringBuilder, then return the code string.
            indentedWriter.Flush ()
            sb.ToString ()

    /// Prints a tree as F# code which, when executed, will re-create the tree.
    static member private ToCodeStringImpl (tree : AvlTree<'T>, indentedWriter : IndentedTextWriter) : unit =
        match tree with
        | Empty ->
            Printf.fprintf indentedWriter "Empty"
        
        | Node (l, r, n, h) ->
            // Write the constructor for this Node.
            Printf.fprintf indentedWriter "Node ("

            // Increase the indentation level _before_ writing the constructor arguments.
            // This ensures the new indentation level will be used when printing the first argument's value.
            let originalIndent = indentedWriter.Indent
            indentedWriter.Indent <- originalIndent + 1
            indentedWriter.WriteLine ()

            // Print the left subtree.
            AvlTree.ToCodeStringImpl (l, indentedWriter)
            indentedWriter.WriteLine ","

            // Print the right subtree.
            AvlTree.ToCodeStringImpl (r, indentedWriter)
            indentedWriter.WriteLine ","

            // Print the value carried within this Node.
            Printf.fprintf indentedWriter "%A" n
            indentedWriter.WriteLine ","

            // Print the height of this Node.
            Printf.fprintf indentedWriter "%uu" h

            // Decrease the indentation level _before_ writing the constructor arguments.
            // This ensures the indentation level will be back to it's original value when this function returns.
            indentedWriter.Indent <- originalIndent

            // Close the constructor.
            // Don't write a newline here -- it'll be written when this function returns.
            indentedWriter.Write ")"

    #if DEBUG
    /// Internal. Only for use with [<StructuredFormatDisplay>].
    member private this.DisplayFormatted
        with get () = AvlTree.ToCodeString this
    #endif

    /// <inherit />
    override this.ToString () =
        let str = AvlTree.ToCodeString this

        // Flatten the string for better printing.
        str.Replace (System.Environment.NewLine, "")

//
and [<Sealed>]
    internal AvlTreeDebuggerProxy<'T when 'T : comparison> (avlTree : AvlTree<'T>) =

    [<DebuggerBrowsable(DebuggerBrowsableState.RootHidden)>]
    member __.Items
        with get () : 'T[] =
            AvlTree.ToArray avlTree
               

/// A Discrete Interval Encoding Tree (DIET) specialized to the 'char' type.
/// This is abbreviated in our documentation as a 'char-DIET'.
type CharDiet = AvlTree<char * char>

/// Functional operations for char-DIETs.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module CharDiet =
    open System.Collections.Generic
    open LanguagePrimitives

    /// Character interval comparer.
    let comparer =
        LanguagePrimitives.FastGenericComparer<char * char>

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
    let inline private dist (x : char) (y : char) : int =
        #if CHECKED_ARITHMETIC
        int (Checked.(-) (uint32 y) (uint32 x))
        #else
        int (uint32 y - uint32 x)
        #endif

    /// Similar to 'pred', but clamps the value to a specified lower limit.
    let inline private clampedPred (lowerBound : char) (c : char) =
        if lowerBound < c then
            pred c
        else c

    /// Similar to 'succ', but clamps the value to a specified upper limit.
    let inline private clampedSucc (upperBound : char) (c : char) =
        if upperBound > c then
            succ c
        else c

    /// Similar to 'pred', but does not allow the value to underflow.
    let inline private safePred (c : char) =
        clampedPred System.Char.MinValue c

    /// Similar to 'succ', but does not allow the value to overflow.
    let inline private safeSucc (c : char) =
        clampedSucc System.Char.MaxValue c

    /// Returns the height of a CharDiet.
    let rec private computeHeight (tree : CharDiet) =
        match tree with
        | Empty -> 0u
        | Node (l, r, _, _) ->
            1u + max (computeHeight l) (computeHeight r)

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

    //
    // NOTE : This function is only called by 'addRange'.
    let rec private find_del_left p (tree : CharDiet) : char * CharDiet =
        // Preconditions
        //assert (dietInvariant tree)
        //assert (intervalsDisjoint tree)

        match tree with
        | Empty ->
            p, Empty
        | Node (left, right, (x, y), _) ->
            if p > safeSucc y then
                let p', right' = find_del_left p right
                p', CharDiet.Join (comparer, left, right', (x, y))
            elif p < x then
                find_del_left p left
            else
                x, left

    //
    // NOTE : This function is only called by 'addRange'.
    let rec private find_del_right p (tree : CharDiet) : char * CharDiet =
        // Preconditions
        //assert (dietInvariant tree)
        //assert (intervalsDisjoint tree)

        match tree with
        | Empty ->
            p, Empty
        | Node (left, right, (x, y), _) ->
            if p < safePred x then
                let p', left' = find_del_right p left
                p', CharDiet.Join (comparer, left', right, (x, y))
            elif p > y then
                find_del_right p right
            else
                y, right

    /// An empty DIET.
    let empty : CharDiet =
        CharDiet.Empty

    /// Determines if a DIET is empty.
    let inline isEmpty (tree : CharDiet) =
        CharDiet.IsEmptyTree tree

    /// Determines if a DIET contains a specified value.
    let rec contains value (tree : CharDiet) =
        // Preconditions
        //assert (dietInvariant tree)
        //assert (intervalsDisjoint tree)

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
        // Preconditions
        //assert (dietInvariant tree)
        //assert (intervalsDisjoint tree)

        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | tree ->
            snd <| CharDiet.MaxElement tree
    
    /// Gets the minimum (least) value stored in the DIET.
    let minElement (tree : CharDiet) : char =
        // Preconditions
        //assert (dietInvariant tree)
        //assert (intervalsDisjoint tree)

        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | tree ->
            fst <| CharDiet.MinElement tree

    /// Gets the minimum (least) and maximum (greatest) values store in the DIET.
    let bounds (tree : CharDiet) : char * char =
        // Preconditions
        //assert (dietInvariant tree)
        //assert (intervalsDisjoint tree)

        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | tree ->
            minElement tree, maxElement tree

    /// Comparison function for DIETs.
    let inline comparison (t1 : CharDiet) (t2 : CharDiet) =
        CharDiet.Compare (comparer, t1, t2)

    /// Equality function for DIETs.
    let inline equal (t1 : CharDiet) (t2 : CharDiet) =
        comparison t1 t2 = 0

    /// Returns the number of elements in the set.
    let count (tree : CharDiet) =
        // Preconditions
        //assert (dietInvariant tree)
        //assert (intervalsDisjoint tree)

        let rec cardinal_aux acc = function
            | [] -> acc
            | Empty :: ts ->
                cardinal_aux acc ts
            | Node (left, right, (x, y), _) :: ts ->
                let d = dist x y
                cardinal_aux (acc + d + 1) (left :: right :: ts)
        
        cardinal_aux 0 [tree]

    /// Returns the number of intervals in the set.
    let intervalCount (tree : CharDiet) =
        // Preconditions
        //assert (dietInvariant tree)
        //assert (intervalsDisjoint tree)

        // OPTIMIZE : Modify this to use a mutable stack instead of an F# list.
        let rec cardinal_aux acc = function
            | [] -> acc
            | Empty :: ts ->
                cardinal_aux acc ts
            | Node (left, right, _, _) :: ts ->
                cardinal_aux (acc + 1) (left :: right :: ts)
        
        cardinal_aux 0 [tree]

    /// Creates a DIET containing the specified value.
    let singleton value : CharDiet =
        CharDiet.Singleton (value, value)

    /// Creates a DIET containing the specified range of values.
    let ofRange (a, b) : CharDiet =
        if a > b then
            invalidArg "b" "The upper bound of the interval is less than the lower bound."

        CharDiet.Singleton (a, b)

    /// Returns a new set with the specified value added to the set.
    /// No exception is thrown if the set already contains the value.
    let rec add value (tree : CharDiet) : CharDiet =
        // Preconditions
        //assert (dietInvariant tree)
        //assert (intervalsDisjoint tree)

        match tree with
        | Empty ->
            singleton value
        | Node (left, right, (x, y), _) ->
            if value >= x then
                if value <= y then
                    // The value is already in [x, y] so the tree
                    // does not need to be modified.
                    tree
                elif value > safeSucc y then
                    // The value is above the interval and is not adjacent
                    // to it, so recurse down the right subtree to add the value
                    // then join the result with the left subtree.
                    CharDiet.Join (comparer, left, add value right, (x, y))
                else
                    match right with
                    | Empty ->
                        //CharDiet.Create (left, Empty, (x, value))
                        CharDiet.Join (comparer, left, Empty, (x, value))
                    | _ ->
                        let (u, v), r = CharDiet.DeleteMin right
                        if safePred u = value then
                            CharDiet.Join (comparer, left, r, (x, v))
                        else
                            //CharDiet.Create (left, right, (x, value))
                            CharDiet.Join (comparer, left, right, (x, value))

            elif value < safePred x then
                CharDiet.Join (comparer, add value left, right, (x, y))
            else
                match left with
                | Empty ->
                    //CharDiet.Create (Empty, right, (value, y))
                    CharDiet.Join (comparer, Empty, right, (value, y))
                | _ ->
                    let (u, v), l = CharDiet.DeleteMax left
                    if safeSucc v = value then
                        CharDiet.Join (comparer, l, right, (u, y))
                    else
                        //CharDiet.Create (left, right, (value, y))
                        CharDiet.Join (comparer, left, right, (value, y))

    /// Returns a new set with the specified range of values added to the set.
    /// No exception is thrown if any of the values are already contained in the set.
    let rec addRange (a, b) (tree : CharDiet) : CharDiet =
        // Preconditions
        if a > b then
            invalidArg "b" "The upper bound of the interval is less than the lower bound."
        //assert (dietInvariant tree)
        //assert (intervalsDisjoint tree)

        match tree with
        | Empty ->
            CharDiet.Singleton (a, b)
        | Node (left, right, (x, y), _) ->
            if b < safePred x then
                let left' = addRange (a, b) left
                CharDiet.Join (comparer, left', right, (x, y))

            elif a > safeSucc y then
                let right' = addRange (a, b) right
                CharDiet.Join (comparer, left, right', (x, y))

            else
                // Now, we know the interval (a, b) being inserted either overlaps or is
                // adjancent to the current inverval (x, y), so we merge them.
                let x', left' =
                    if a >= x then x, left
                    else find_del_left a left
                let y', right' =
                    if b <= y then y, right
                    else find_del_right b right

                CharDiet.Join (comparer, left', right', (x', y'))

    /// Returns a new set with the given element removed.
    /// No exception is thrown if the set doesn't contain the specified element.
    let rec remove value (tree : CharDiet) : CharDiet =
        // Preconditions
        //assert (dietInvariant tree)
        //assert (intervalsDisjoint tree)

        match tree with
        | Empty ->
            Empty
        | Node (left, right, (x, y), _) ->
            let czx = compare value x
            if czx < 0 then
                // value < x, so recurse down the left subtree.
                CharDiet.Join (comparer, remove value left, right, (x, y))
            else
                let cyz = compare y value
                if cyz < 0 then
                    // y < value, so recurse down the right subtree.
                    CharDiet.Join (comparer, left, remove value right, (x, y))
                elif cyz = 0 then
                    if czx = 0 then
                        CharDiet.Reroot (comparer, left, right)
                    else
                        //CharDiet.Create (left, right, (x, safePred y))
                        CharDiet.Join (comparer, left, right, (x, safePred y))
                elif czx = 0 then
                    //CharDiet.Create (left, right, (safeSucc x, y))
                    CharDiet.Join (comparer, left, right, (safeSucc x, y))
                else
                    //CharDiet.Create (left, right, (x, safePred value))
                    CharDiet.Join (comparer, left, right, (x, safePred value))
                    |> addRange (safeSucc value, y)

    /// Determines if a value is greater than or equal to a given
    /// limit value if one is specified.
    let private greater_limit limit value =
        match limit with
        | None -> false
        | Some limit ->
            value >= limit

    /// Recursive implementation function for computing the union of two sets.
    let rec private unionImpl (input : CharDiet) limit head (stream : CharDiet)
        : CharDiet * (char * char) option * CharDiet =
        // Preconditions
        //assert (CharDiet.Height input >= CharDiet.Height stream)  // Keep this!
//        assert (dietInvariant input)
//        assert (dietInvariant stream)
//        assert (intervalsDisjoint input)
//        assert (intervalsDisjoint stream)

        match head, input with
        | None, _ ->
            input, None, Empty
        | _, Empty ->
            Empty, head, stream
        | Some (x, _), Node (left, right, (a, b), _) ->
//            assert (dietInvariant left)
//            assert (dietInvariant right)
//            assert (intervalsDisjoint left)
//            assert (intervalsDisjoint right)

            let left', head, stream' =
                if x < a then
                    unionImpl left (Some <| safePred a) head stream
                else
                    left, head, stream
            unionHelper left' (a, b) right limit head stream'

    /// Helper function for computing the union of two sets.
    and private unionHelper left (a, b) (right : CharDiet) limit head stream =
        // Preconditions
        if a > b then
            invalidArg "b" "The upper bound of the interval is less than the lower bound."
//        assert (dietInvariant left)
//        assert (dietInvariant right)
//        assert (dietInvariant stream)
//        assert (intervalsDisjoint left)
//        assert (intervalsDisjoint right)
//        assert (intervalsDisjoint stream)

        match head with
        | None ->
            CharDiet.Join (comparer, left, right, (a, b)), None, Empty
        | Some (x, y) ->
            if y < a && y < safePred a then
                let left' = addRange (x, y) left
                CharDiet.TryDeleteMin stream
                ||> unionHelper left' (a, b) right limit

            elif x > b && x > safeSucc b then
                let right', head, stream = unionImpl right limit head stream
                CharDiet.Join (comparer, left, right', (a, b)), head, stream

            elif b >= y then
                CharDiet.TryDeleteMin stream
                ||> unionHelper left (min a x, b) right limit

            elif greater_limit limit y then
                left, Some (min a x, y), stream

            else
                let right', head, stream = unionImpl right limit (Some (min a x, y)) stream
                CharDiet.Reroot (comparer, left, right'), head, stream

    /// Computes the union of the two sets.
    let rec union (input : CharDiet) (stream : CharDiet) : CharDiet =
        // Preconditions
//        assert (dietInvariant input)
//        assert (dietInvariant stream)
//        assert (intervalsDisjoint input)
//        assert (intervalsDisjoint stream)

        match input, stream with
        | Empty, set
        | set, Empty ->
            set
        | Node (_,_,_,inputHeight), Node (_,_,_,streamHeight)
            when streamHeight > inputHeight ->
            union stream input
        | _, _ ->
//            #if DEBUG
//            let inputCount = count input
//            let streamCount = count stream
//            /// The minimum possible number of elements in the resulting set.
//            let minPossibleResultCount =
//                max inputCount streamCount
//            /// The maximum possible number of elements in the resulting set.
//            let maxPossibleResultCount =
//                inputCount + streamCount
//            #endif

            let result =
                let result, head', stream'' =
                    CharDiet.TryDeleteMin stream
                    ||> unionImpl input None

                match head' with
                | None ->
                    result
                | Some i ->
                    CharDiet.Join (comparer, result, stream'', i)

//            Debug.Assert (
//                dietInvariant result,
//                "The DIET invariant does not hold for the result.")
//            Debug.Assert (
//                intervalsDisjoint result,
//                "The intervals in the DIET are not disjoint.")

//            #if DEBUG
//            let resultCount = count result
//            Debug.Assert (
//                resultCount >= minPossibleResultCount,
//                sprintf "The result set should not contain fewer than %i elements, but it contains only %i elements."
//                    minPossibleResultCount resultCount)
//            Debug.Assert (
//                resultCount <= maxPossibleResultCount,
//                sprintf "The result set should not contain more than %i elements, but it contains %i elements."
//                    maxPossibleResultCount resultCount)
//            #endif
            result

    /// Recursive implementation function for computing the intersection of two sets.
    let rec private intersectImpl (input : CharDiet) head (stream : CharDiet) : CharDiet * (char * char) option * CharDiet =
        // Preconditions
        //assert (CharDiet.Height input >= CharDiet.Height stream)  // Should we keep this?
//        assert (dietInvariant input)
//        assert (dietInvariant stream)
//        assert (intervalsDisjoint input)
//        assert (intervalsDisjoint stream)

        match head, input with
        | None, _ ->
            Empty, None, Empty
        | _, Empty ->
            Empty, head, stream
        | Some (x, _), Node (left, right, (a, b), _) ->
            let left', head, stream' =
                if x < a then
                    intersectImpl left head stream
                else
                    Empty, head, stream

            intersectHelper (a, b) right left' head stream'

    /// Helper function for computing the intersection of two sets.
    and private intersectHelper (a, b) (right : CharDiet) (left : CharDiet) head stream =
        // Preconditions
        if a > b then
            invalidArg "b" "The upper bound of the interval is less than the lower bound."
//        assert (dietInvariant left)
//        assert (dietInvariant right)
//        assert (dietInvariant stream)
//        assert (intervalsDisjoint left)
//        assert (intervalsDisjoint right)
//        assert (intervalsDisjoint stream)

        match head with
        | None ->
            left, None, Empty

        | Some (x, y) ->
            if y < a then
                match stream with
                | Empty ->
                    left, None, Empty
                | _ ->
                    CharDiet.TryDeleteMin stream
                    ||> intersectHelper (a, b) right left

            elif b < x then
                let right, head, stream = intersectImpl right head stream
                CharDiet.Reroot (comparer, left, right), head, stream

            elif y >= clampedPred y b then
                let right, head, stream = intersectImpl right head stream
                let right' = CharDiet.Join (comparer, left, right, (max x a, min y b))
                right', head, stream

            else
                let left = addRange (max x a, y) left
                intersectHelper (safeSucc y, b) right left head stream

    /// Computes the intersection of the two sets.
    let rec intersect (input : CharDiet) (stream : CharDiet) : CharDiet =
        // Preconditions
//        assert (dietInvariant input)
//        assert (dietInvariant stream)
//        assert (intervalsDisjoint input)
//        assert (intervalsDisjoint stream)

        match input, stream with
        | Empty, _
        | _, Empty ->
            Empty
        | Node (_,_,_,inputHeight), Node(_,_,_,streamHeight)
            when streamHeight > inputHeight ->
            intersect stream input
        | _, _ ->
//            #if DEBUG
//            /// The maximum possible number of elements in the resulting set.
//            let maxPossibleResultCount =
//                let inputCount = count input
//                let streamCount = count stream
//                inputCount + streamCount
//            #endif

            let result, _, _ =
                CharDiet.TryDeleteMin stream
                ||> intersectImpl input
            
//            Debug.Assert (
//                dietInvariant result,
//                "The DIET invariant does not hold for the result.")
//            Debug.Assert (
//                intervalsDisjoint result,
//                "The intervals in the DIET are not disjoint.")

//            #if DEBUG
//            let resultCount = count result
//
//            Debug.Assert (
//                resultCount <= maxPossibleResultCount,
//                sprintf "The result set should not contain more than %i elements, but it contains %i elements."
//                    maxPossibleResultCount resultCount)
//            #endif
            result

    /// Recursive implementation function for computing the difference of two sets.
    let rec private diffImpl (input : CharDiet) head (stream : CharDiet) : CharDiet * (char * char) option * CharDiet =
        // Preconditions
//        assert (dietInvariant input)
//        assert (dietInvariant stream)
//        assert (intervalsDisjoint input)
//        assert (intervalsDisjoint stream)

        match head, input with
        | None, _->
            input, None, Empty
        | _, Empty ->
            Empty, head, stream
        | Some (x, _), Node (left, right, (a, b), _) ->
            let left, head, stream =
                if x < a then
                    diffImpl left head stream
                else
                    left, head, stream
            diffHelper (a, b) right left head stream

    /// Helper function for computing the difference of two sets.
    and private diffHelper (a, b) (right : CharDiet) (left : CharDiet) head stream =
        // Preconditions
        if a > b then
            invalidArg "b" "The upper bound of the interval is less than the lower bound."
//        assert (dietInvariant left)
//        assert (dietInvariant right)
//        assert (dietInvariant stream)
//        assert (intervalsDisjoint left)
//        assert (intervalsDisjoint right)
//        assert (intervalsDisjoint stream)

        match head with
        | None ->
            CharDiet.Join (comparer, left, right, (a, b)), None, Empty
        | Some (x, y) ->
            if y < a then
                // [x, y] and [a, b] are disjoint
                CharDiet.TryDeleteMin stream
                ||> diffHelper (a, b) right left
            elif b < x then
                // [a, b] and [x, y] are disjoint
                let right, head, stream = diffImpl right head stream
                CharDiet.Join (comparer, left, right, (a, b)), head, stream
            elif a < x then
                // [a, b] and [x, y] overlap
                // a < x
                diffHelper (x, b) right ((addRange (a, safePred x) left)) head stream
            elif y < b then
                // [a, b] and [x, y] overlap
                // y < b
                CharDiet.TryDeleteMin stream
                ||> diffHelper (safeSucc y, b) right left
            else
                // [a, b] and [x, y] overlap
                let right, head, stream = diffImpl right head stream
                CharDiet.Reroot (comparer, left, right), head, stream

    /// Returns a new set with the elements of the second set removed from the first.
    let difference (input : CharDiet) (stream : CharDiet) : CharDiet =
        // Preconditions
//        assert (dietInvariant input)
//        assert (dietInvariant stream)
//        assert (intervalsDisjoint input)
//        assert (intervalsDisjoint stream)

        match input, stream with
        | Empty, _ ->
            Empty
        | _, Empty ->
            input
        | _, _ ->
//            #if DEBUG
//            /// The maximum possible number of elements in the resulting set.
//            let maxPossibleResultCount = count input
//            #endif

            let result, _, _ =
                CharDiet.TryDeleteMin stream
                ||> diffImpl input
            
//            Debug.Assert (
//                dietInvariant result,
//                "The DIET invariant does not hold for the result.")
//            Debug.Assert (
//                intervalsDisjoint result,
//                "The intervals in the DIET are not disjoint.")

//            #if DEBUG
//            let resultCount = count result
//            Debug.Assert (
//                resultCount <= maxPossibleResultCount,
//                sprintf "The result set should not contain more than %i elements, but it contains %i elements."
//                    maxPossibleResultCount resultCount)
//            #endif
            result

    /// Applies the given accumulating function to all elements in a DIET.
    let fold (folder : 'State -> char -> 'State) (state : 'State) (tree : CharDiet) =
        // Preconditions
//        assert (dietInvariant tree)
//        assert (intervalsDisjoint tree)

        let folder = FSharpFunc<_,_,_>.Adapt folder

        let rangeFolder (state : 'State) (lo, hi) =
            // Fold over the items in increasing order.
            let mutable state = state
            for x = int lo to int hi do
                state <- folder.Invoke (state, char x)
            state

        CharDiet.Fold rangeFolder state tree

    /// Applies the given accumulating function to all elements in a DIET.
    let foldBack (folder : char -> 'State -> 'State) (tree : CharDiet) (state : 'State) =
        // Preconditions
//        assert (dietInvariant tree)
//        assert (intervalsDisjoint tree)

        let folder = FSharpFunc<_,_,_>.Adapt folder

        let rangeFolder (lo, hi) (state : 'State) =
            // Fold over the items in decreasing order.
            let mutable state = state
            for x = int hi downto int lo do
                state <- folder.Invoke (char x, state)
            state

        CharDiet.FoldBack rangeFolder state tree

    /// Applies the given function to all elements in a DIET.
    let iter (action : char -> unit) (tree : CharDiet) =
        // Preconditions
//        assert (dietInvariant tree)
//        assert (intervalsDisjoint tree)

        /// Applies the action to all values within an interval.
        let intervalApplicator (lo, hi) =
            for x = int lo to int hi do
                action (char x)

        CharDiet.Iter intervalApplicator tree

    //
    let forall (predicate : char -> bool) (tree : CharDiet) =
        // Preconditions
//        assert (dietInvariant tree)
//        assert (intervalsDisjoint tree)

        // OPTIMIZE : Rewrite this to short-circuit and return early
        // if we find a non-matching element.
        (true, tree)
        ||> fold (fun state el ->
            state && predicate el)

    //
    let exists (predicate : char -> bool) (tree : CharDiet) =
        // Preconditions
//        assert (dietInvariant tree)
//        assert (intervalsDisjoint tree)

        // OPTIMIZE : Rewrite this to short-circuit and return early
        // if we find a non-matching element.
        (false, tree)
        ||> fold (fun state el ->
            state || predicate el)

    //
    let rec toSeq (tree : CharDiet) =
        // Preconditions
//        assert (dietInvariant tree)
//        assert (intervalsDisjoint tree)

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
        // Preconditions
//        assert (dietInvariant tree)
//        assert (intervalsDisjoint tree)

        ([], tree)
        ||> fold (fun list el ->
            el :: list)

    //
    let toArray (tree : CharDiet) =
        // Preconditions
//        assert (dietInvariant tree)
//        assert (intervalsDisjoint tree)

        let elements = ResizeArray ()
        iter elements.Add tree
        elements.ToArray ()

    //
    let toSet (tree : CharDiet) =
        // Preconditions
//        assert (dietInvariant tree)
//        assert (intervalsDisjoint tree)

        (Set.empty, tree)
        ||> fold (fun set el ->
            Set.add el set)


/// <summary>
/// Character set implementation based on a Discrete Interval Encoding Tree.
/// This is faster and more efficient than the built-in F# <see cref="T:Set&lt;T&gt;"/>,
/// especially for dense sets.
/// </summary>
[<Sealed>]
[<DebuggerDisplay("Count = {Count}, Intervals = {IntervalCount}")>]
type CharSet private (tree : CharDiet) as this =
    /// The empty CharSet.
    static let empty = CharSet (CharDiet.empty)
    /// The "full" CharSet, i.e., a CharSet containing all possible values.
    static let universe =
        CharSet.AddRange (Char.MinValue, Char.MaxValue, empty)

    /// The hash code for this CharSet is lazily computed,
    /// then cached for maximum performance.
    let hashCode = lazy (CharSet.ComputeHash this)

    /// Returns an empty CharSet instance.
    static member Empty
        with get () = empty

    /// <summary>Returns a <see cref="T:CharSet"/> instance containing all possible <see cref="T:System.Char"/> values.</summary>
    static member Universe
        with get () = universe
    
    override this.GetHashCode () =
        Lazy.force hashCode

    override this.Equals other =
        match other with
        | :? CharSet as other ->
            this == other ||
            tree == other.Tree ||
            CharDiet.equal tree other.Tree
        | _ ->
            false

    //
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
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
        let result = CharDiet.singleton value
//        assert (CharDiet.dietInvariant result)
//        assert (CharDiet.intervalsDisjoint result)
        CharSet (result)

    /// The set containing the elements in the given range.
    static member FromRange (lowerBound, upperBound) : CharSet =
        // For compatibility with the F# range operator, return an empty
        // set for an inverted range (i.e., when lowerBound > upperBound).
        if lowerBound > upperBound then empty
        elif lowerBound = upperBound then
            // This is a single-element range.
            CharSet.FromElement lowerBound
        else
            let result = CharDiet.ofRange (lowerBound, upperBound)
            //assert (CharDiet.dietInvariant result)
            //assert (CharDiet.intervalsDisjoint result)
            CharSet (result)

    //
    static member IsEmpty (charSet : CharSet) : bool =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        CharDiet.isEmpty charSet.Tree

    /// Returns a new set with an element added to the set.
    /// No exception is raised if the set already contains the given element.
    static member Add (value, charSet : CharSet) : CharSet =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        // OPTIMIZATION : If the resulting tree is the same as the original, return
        // the input set instead of creating a new set.
        let result = CharDiet.add value charSet.Tree
        //assert (CharDiet.dietInvariant result)
        //assert (CharDiet.intervalsDisjoint result)
        if charSet.Tree == result then charSet
        else CharSet (result)

    //
    static member AddRange (lower, upper, charSet : CharSet) : CharSet =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        // For compatibility with the F# range operator, we don't raise
        // an exception if lower > upper; that is considered an empty range,
        // so here we just return the input set without modifying it.
        if lower > upper then charSet
        elif lower = upper then
            // Add the single value to the tree.
            CharSet.Add (lower, charSet)
        else
            // lower < upper
            // OPTIMIZATION : If the resulting tree is the same as the original,
            // return the input set instead of creating a new set.
            let result = CharDiet.addRange (lower, upper) charSet.Tree
            //assert (CharDiet.dietInvariant result)
            //assert (CharDiet.intervalsDisjoint result)
            if charSet.Tree == result then charSet
            else CharSet (result)

    //
    static member Remove (value, charSet : CharSet) : CharSet =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        // OPTIMIZATION : If the resulting tree is the same as the original,
        // return the input set instead of creating a new set.
        let result = CharDiet.remove value charSet.Tree
        //assert (CharDiet.dietInvariant result)
        //assert (CharDiet.intervalsDisjoint result)
        if charSet.Tree == result then charSet
        else CharSet (result)

    //
    static member Contains (value, charSet : CharSet) : bool =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        CharDiet.contains value charSet.Tree

    //
    static member OfSeq (sequence : seq<char>) : CharSet =
        // Preconditions
        checkNonNull "sequence" sequence

        // If the sequence is empty, return immediately.
        if Seq.isEmpty sequence then empty
        else
            let tree =
                (Empty, sequence)
                ||> Seq.fold (fun tree el ->
                    CharDiet.add el tree)
            //assert (CharDiet.dietInvariant tree)
            //assert (CharDiet.intervalsDisjoint tree)
            CharSet (tree)

    //
    static member OfList (list : char list) : CharSet =
        // Preconditions
        checkNonNull "list" list

        // If the list is empty, return immediately.
        if List.isEmpty list then empty
        else
            let tree =
                (Empty, list)
                ||> List.fold (fun tree el ->
                    CharDiet.add el tree)
            //assert (CharDiet.dietInvariant tree)
            //assert (CharDiet.intervalsDisjoint tree)
            CharSet (tree)

    //
    static member OfArray (array : char[]) : CharSet =
        // Preconditions
        checkNonNull "array" array

        // If the array is empty, return immediately.
        if Array.isEmpty array then empty
        else
            let tree =
                (Empty, array)
                ||> Array.fold (fun tree el ->
                    CharDiet.add el tree)
            //assert (CharDiet.dietInvariant tree)
            //assert (CharDiet.intervalsDisjoint tree)
            CharSet (tree)

    //
    static member OfSet (set : Set<char>) : CharSet =
        // Preconditions
        checkNonNull "set" set

        // If the set is empty, return immediately.
        if Set.isEmpty set then empty
        else
            let tree =
                (Empty, set)
                ||> Set.fold (fun tree el ->
                    CharDiet.add el tree)
            //assert (CharDiet.dietInvariant tree)
            //assert (CharDiet.intervalsDisjoint tree)
            CharSet (tree)

    //
    static member ToSeq (charSet : CharSet) : seq<char> =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        CharDiet.toSeq charSet.Tree

    //
    static member ToList (charSet : CharSet) : char list =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        CharDiet.toList charSet.Tree

    //
    static member ToArray (charSet : CharSet) : char[] =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        CharDiet.toArray charSet.Tree

    //
    static member ToSet (charSet : CharSet) : Set<char> =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        CharDiet.toSet charSet.Tree

    //
    static member Difference (charSet1 : CharSet, charSet2 : CharSet) : CharSet =
        // Preconditions
        checkNonNull "charSet1" charSet1
        checkNonNull "charSet2" charSet2
        //assert (CharDiet.dietInvariant charSet1.Tree)
        //assert (CharDiet.dietInvariant charSet2.Tree)
        //assert (CharDiet.intervalsDisjoint charSet1.Tree)
        //assert (CharDiet.intervalsDisjoint charSet2.Tree)

        // If the input sets have the same underlying tree, we can return immediately.
        if charSet1.Tree == charSet2.Tree then CharSet.Empty
        else
            // OPTIMIZATION : If the result is the same as either input set's tree,
            // return that set instead of creating a new one.
            let result = CharDiet.difference charSet1.Tree charSet2.Tree
            //assert (CharDiet.dietInvariant result)
            //assert (CharDiet.intervalsDisjoint result)
            if charSet1.Tree == result then charSet1
            elif charSet2.Tree == result then charSet2
            else CharSet (result)

    //
    static member Intersect (charSet1 : CharSet, charSet2 : CharSet) : CharSet =
        // Preconditions
        checkNonNull "charSet1" charSet1
        checkNonNull "charSet2" charSet2
        //assert (CharDiet.dietInvariant charSet1.Tree)
        //assert (CharDiet.dietInvariant charSet2.Tree)
        //assert (CharDiet.intervalsDisjoint charSet1.Tree)
        //assert (CharDiet.intervalsDisjoint charSet2.Tree)

        // If the input sets have the same underlying tree, we can return immediately.
        if charSet1.Tree == charSet2.Tree then charSet1
        else
            // OPTIMIZATION : If the result is the same as either input set's tree,
            // return that set instead of creating a new one.
            let result = CharDiet.intersect charSet1.Tree charSet2.Tree
            //assert (CharDiet.dietInvariant result)
            //assert (CharDiet.intervalsDisjoint result)
            if charSet1.Tree == result then charSet1
            elif charSet2.Tree == result then charSet2
            else CharSet (result)

    //
    static member Union (charSet1 : CharSet, charSet2 : CharSet) : CharSet =
        // Preconditions
        checkNonNull "charSet1" charSet1
        checkNonNull "charSet2" charSet2
        //assert (CharDiet.dietInvariant charSet1.Tree)
        //assert (CharDiet.dietInvariant charSet2.Tree)
        //assert (CharDiet.intervalsDisjoint charSet1.Tree)
        //assert (CharDiet.intervalsDisjoint charSet2.Tree)

        // If the input sets have the same underlying tree, we can return immediately.
        if charSet1.Tree == charSet2.Tree then charSet1
        else
            // OPTIMIZATION : If the result is the same as either input set's tree,
            // return that set instead of creating a new one.
            let result = CharDiet.union charSet1.Tree charSet2.Tree
            //assert (CharDiet.dietInvariant result)
            //assert (CharDiet.intervalsDisjoint result)
            if charSet1.Tree == result then charSet1
            elif charSet2.Tree == result then charSet2
            else CharSet (result)

    //
    static member Complement (charSet : CharSet) : CharSet =
        // Preconditions
        checkNonNull "charSet" charSet

        // OPTIMIZATION : If the given CharSet is the empty set or universe, we don't need to perform the actual computation.
        if charSet == empty then universe
        elif charSet == universe then empty
        else
            // Compute the complement of the given set by 'subtracting' the given CharSet from the universe set.
            CharSet.Difference (universe, charSet)

    //
    static member Exists (predicate, charSet : CharSet) : bool =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        CharDiet.exists predicate charSet.Tree

    //
    static member Forall (predicate, charSet : CharSet) : bool =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        CharDiet.forall predicate charSet.Tree

    /// Applies the given accumulating function to all elements in a DIET.
    static member Fold (folder : 'State -> _ -> 'State, state, charSet : CharSet) : 'State =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        CharDiet.fold folder state charSet.Tree

    /// Applies the given accumulating function to all elements in a DIET.
    static member FoldBack (folder : _ -> 'State -> 'State, state, charSet : CharSet) : 'State =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        CharDiet.foldBack folder charSet.Tree state

    /// Applies the given accumulating function to all intervals in a DIET.
    static member FoldIntervals (folder : 'State -> char * char -> 'State, state, charSet : CharSet) : 'State =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        let folder = FSharpFunc<_,_,_>.Adapt folder
        AvlTree.Fold folder.Invoke state charSet.Tree

    //
    static member private ComputeHash (charSet : CharSet) =
        (* The HashMap type is used throughout FSharpLex for performance reasons;
           this function must return a "robust" hash code -- i.e., one which causes
           a very low number of conflicts -- because otherwise performance will be
           *severely* affected. *)
        CharSet.FoldIntervals (
            (fun hashCode (lo, hi) ->
//                // Compute a value for this interval by simply packing the characters
//                // into a 32-bit value as [hi, lo].
//                let intervalHash = int (((uint32 hi) <<< 16) &&& uint32 lo)

                // Compute a value for this interval using the Cantor pairing function.
                let intervalHash =
                    let k1k2 = int lo + int hi
                    ((k1k2 * (k1k2 + 1)) / 2) + (int hi)

                // Combine the interval hash with the current hash code to produce a new hash code.
                (hashCode <<< 1) + intervalHash + 631),
            19, charSet)

    //
    static member Iter (action, charSet : CharSet) : unit =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        CharDiet.iter action charSet.Tree

    //
    static member IterIntervals (action, charSet : CharSet) : unit =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        let action = FSharpFunc<_,_,_>.Adapt action
        charSet.Tree |> AvlTree.Iter action.Invoke

    //
    static member Map (mapping : char -> char, charSet : CharSet) : CharSet =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        let mappedTree =
            (CharDiet.empty, charSet.Tree)
            ||> CharDiet.fold (fun mappedTree ch ->
                CharDiet.add (mapping ch) mappedTree)

        CharSet (mappedTree)

    //
    static member Filter (predicate : char -> bool, charSet : CharSet) : CharSet =
        // Preconditions
        checkNonNull "charSet" charSet
        //assert (CharDiet.dietInvariant charSet.Tree)
        //assert (CharDiet.intervalsDisjoint charSet.Tree)

        let filteredTree =
            (charSet.Tree, charSet.Tree)
            ||> CharDiet.fold (fun filteredTree ch ->
                if predicate ch then
                    filteredTree
                else
                    CharDiet.remove ch filteredTree)

        // OPTIMIZATION : If the filtered tree is the same as the input set's tree,
        // return the input set instead of creating a new CharSet with the same tree.
        if charSet.Tree == filteredTree then charSet
        else CharSet (filteredTree)

    override this.ToString () =
        if CharSet.IsEmpty this then "{}"
        else
            let sb = System.Text.StringBuilder ()
            sb.Append "{" |> ignore

            // Write each of the intervals into the StringBuilder.
            CharSet.IterIntervals ((fun lo hi ->
                Printf.bprintf sb "\u%04x-\u%04x, " (int lo) (int hi)),
                this)

            sb.Length <- sb.Length - 2  // Remove the trailing ", "
            sb.Append "}" |> ignore

            sb.ToString ()

    interface System.IComparable with
        member this.CompareTo other =
            match other with
            | :? CharSet as other ->
                if this == other || this.Tree == other.Tree then 0
                else CharDiet.comparison tree other.Tree
            | _ ->
                invalidArg "other" "The argument is not an instance of CharSet."

    interface System.IComparable<CharSet> with
        member this.CompareTo other =
            if this == other || this.Tree == other.Tree then 0
            else CharDiet.comparison tree other.Tree

    interface System.IEquatable<CharSet> with
        member this.Equals other =
            this == other
            || this.Tree == other.Tree
            || CharDiet.equal tree other.Tree


/// Functional programming operators related to the CharSet type.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module CharSet =
    /// The empty set.
    [<CompiledName("Empty"); GeneralizableValue>]
    let empty = CharSet.Empty

    /// <summary>Returns a <see cref="T:CharSet"/> instance containing all possible <see cref="T:System.Char"/> values.</summary>
    [<CompiledName("Universe"); GeneralizableValue>]
    let universe = CharSet.Universe

    /// Returns 'true' if the set is empty.
    [<CompiledName("IsEmpty")>]
    let inline isEmpty charSet : bool =
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
    let inline maxElement (charSet : CharSet) : char =
        charSet.MaxElement

    /// Returns the lowest (least) value in the set.
    [<CompiledName("MinElement")>]
    let inline minElement (charSet : CharSet) : char =
        charSet.MinElement

    /// The set containing the given element.
    [<CompiledName("Singleton")>]
    let inline singleton c : CharSet =
        CharSet.FromElement c

    /// Evaluates to 'true' if the given element is in the given set.
    [<CompiledName("Contains")>]
    let inline contains value charSet : bool =
        CharSet.Contains (value, charSet)

    /// Returns a new set with an element added to the set.
    /// No exception is raised if the set already contains the given element.
    [<CompiledName("Add")>]
    let inline add value charSet : CharSet =
        CharSet.Add (value, charSet)

    /// Returns a new set with a range of elements added to the set.
    /// No exception is raised if the set already contains any of the elements.
    [<CompiledName("AddRange")>]
    let inline addRange lower upper charSet : CharSet =
        CharSet.AddRange (lower, upper, charSet)

    /// Returns a new set with the given element removed.
    /// No exception is raised if the set doesn't contain the given element.
    [<CompiledName("Remove")>]
    let inline remove value charSet : CharSet =
        CharSet.Remove (value, charSet)

    /// Tests if any element of the collection satisfies the given predicate.
    /// If the input function is <c>predicate</c> and the elements are <c>i0...iN</c>,
    /// then this function computes predicate <c>i0 or ... or predicate iN</c>.
    [<CompiledName("Exists")>]
    let inline exists (predicate : char -> bool) charSet : bool =
        CharSet.Exists (predicate, charSet)

    /// Tests if all elements of the collection satisfy the given predicate.
    /// If the input function is <c>p</c> and the elements are <c>i0...iN</c>,
    /// then this function computes <c>p i0 && ... && p iN</c>.
    [<CompiledName("Forall")>]
    let inline forall (predicate : char -> bool) charSet : bool =
        CharSet.Forall (predicate, charSet)

    /// Applies the given function to each element of the set, in order from least to greatest.
    [<CompiledName("Iter")>]
    let inline iter (action : char -> unit) charSet : unit =
        CharSet.Iter (action, charSet)

    /// Applies the given function to each element of the set, in order from least to greatest.
    [<CompiledName("IterIntervals")>]
    let inline iterIntervals action charSet : unit =
        CharSet.IterIntervals (action, charSet)
    
    /// Applies the given accumulating function to all the elements of the set.
    [<CompiledName("Fold")>]
    let inline fold (folder : 'State -> char -> 'State) (state : 'State) charSet : 'State =
        CharSet.Fold (folder, state, charSet)

    /// Applies the given accumulating function to all the elements of the set.
    [<CompiledName("FoldBack")>]
    let inline foldBack (folder : char -> 'State -> 'State) charSet (state : 'State) : 'State =
        CharSet.FoldBack (folder, state, charSet)

    /// Returns a new set containing the results of applying the given function to each element of the input set.
    [<CompiledName("Map")>]
    let map (mapping : char -> char) charSet : CharSet  =
        CharSet.Map (mapping, charSet)

    /// Returns a new set containing only the elements of the collection for which the given predicate returns true.
    [<CompiledName("Filter")>]
    let inline filter (predicate : char -> bool) charSet : CharSet =
        CharSet.Filter (predicate, charSet)

    /// The set containing the elements in the given range.
    [<CompiledName("OfRange")>]
    let inline ofRange (lowerBound : char) (upperBound : char) : CharSet =
        CharSet.FromRange (lowerBound, upperBound)

    /// Creates a new set from the given enumerable object.
    [<CompiledName("OfSeq")>]
    let inline ofSeq seq : CharSet =
        CharSet.OfSeq seq

    /// Creates a set that contains the same elements as the given list.
    [<CompiledName("OfList")>]
    let inline ofList list : CharSet =
        CharSet.OfList list

    /// Creates a set that contains the same elements as the given array.
    [<CompiledName("OfArray")>]
    let inline ofArray array : CharSet =
        CharSet.OfArray array

    /// Creates a CharSet that contains the same elements as the given Set.
    [<CompiledName("OfSet")>]
    let inline ofSet set : CharSet =
        CharSet.OfSet set

    /// Returns an ordered view of the set as an enumerable object.
    [<CompiledName("ToSeq")>]
    let inline toSeq charSet : seq<char> =
        CharSet.ToSeq charSet

    /// Creates a list that contains the elements of the set in order.
    [<CompiledName("ToList")>]
    let inline toList charSet : char list =
        CharSet.ToList charSet

    /// Creates an array that contains the elements of the set in order.
    [<CompiledName("ToArray")>]
    let inline toArray charSet : char[] =
        CharSet.ToArray charSet

    /// Creates a Set that contains the same elements as the given CharSet.
    [<CompiledName("ToSet")>]
    let inline toSet charSet : Set<char> =
        CharSet.ToSet charSet

    /// Returns a new set with the elements of the second set removed from the first.
    [<CompiledName("Difference")>]
    let inline difference set1 set2 : CharSet =
        CharSet.Difference (set1, set2)

    /// Computes the intersection of the two sets.
    [<CompiledName("Intersect")>]
    let inline intersect set1 set2 : CharSet =
        CharSet.Intersect (set1, set2)

    /// Computes the union of the two sets.
    [<CompiledName("Union")>]
    let inline union set1 set2 : CharSet =
        CharSet.Union (set1, set2)

    /// Computes the complement of the given set.
    [<CompiledName("Complement")>]
    let inline complement charSet : CharSet =
        CharSet.Complement charSet
    