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
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpLex.SpecializedCollections

open System.Diagnostics
open OptimizedClosures
open ExtCore
open ExtCore.Collections
open ExtCore.Control


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
    // OPTIMIZE : This should be re-implemented without continuations --
    // move it into 'computeHeight' and use a mutable stack to traverse the tree.
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
    let rec contains value (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            false
        | Node (n, l, r, _) ->
            let comparison = compare value n
            if comparison = 0 then      // value = n
                true
            elif comparison < 0 then    // value < n
                contains value l
            else                        // value > n
                contains value r

    /// Removes the specified value from the tree.
    /// If the tree doesn't contain the value, no exception is thrown;
    /// the tree will be returned without modification.
    let rec delete x (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            Empty
        | Node (n, l, r, _) as tree ->
            let comparison = compare x n
            if comparison = 0 then      // x = n
                delete_root tree
            elif comparison < 0 then    // x < n
                let la = delete x l
                mkt_bal_r n la r
            else                        // x > n
                let a = delete x r
                mkt_bal_l n l a

    /// Adds a value to an AVL tree.
    /// If the tree already contains the value, no exception is thrown;
    /// the tree will be returned without modification.
    let rec insert x (tree : AvlTree<'T>) =
        match tree with
        | Empty ->
            Node (x, Empty, Empty, 1u)
        | Node (n, l, r, _) as tree ->
            let comparison = compare x n
            if comparison = 0 then      // x = n
                tree
            elif comparison < 0 then    // x < n
                mkt_bal_l n (insert x l) r
            else                        // x > n
                mkt_bal_r n l (insert x r)

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
    let rec extractMin (tree : AvlTree<'T>) =
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
            |> extractMin

    /// Extracts the minimum (least) value from an AVL tree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    let tryExtractMin (tree : AvlTree<'T>) =
        // Is the tree empty?
        if isEmpty tree then
            None, tree
        else
            let minElement, tree = extractMin tree
            Some minElement, tree

    /// Extracts the maximum (greatest) value from an AVL tree,
    /// returning the value along with the updated tree.
    let rec extractMax (tree : AvlTree<'T>) =
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
            |> extractMax

    /// Extracts the maximum (greatest) value from an AVL tree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    let tryExtractMax (tree : AvlTree<'T>) =
        // Is the tree empty?
        if isEmpty tree then
            None, tree
        else
            let maxElement, tree = extractMax tree
            Some maxElement, tree

    /// Merges two AVL trees and returns the result.
    let union (tree1 : AvlTree<'T>) (tree2 : AvlTree<'T>) =
        let tree1_count = count tree1
        let tree2_count = count tree2

        // Merge the smaller set into the larger set.
        if tree1_count < tree2_count then
            (tree2, tree1)
            ||> fold (fun tree el ->
                insert el tree)
        else
            (tree1, tree2)
            ||> fold (fun tree el ->
                insert el tree)

    /// Builds a new AVL tree from the elements of a sequence.
    let ofSeq (sequence : seq<_>) : AvlTree<'T> =
        (Empty, sequence)
        ||> Seq.fold (fun tree el ->
            insert el tree)

    /// Builds a new AVL tree from the elements of an F# list.
    let ofList (list : _ list) : AvlTree<'T> =
        (Empty, list)
        ||> List.fold (fun tree el ->
            insert el tree)

    /// Builds a new AVL tree from the elements of an array.
    let ofArray (array : _[]) : AvlTree<'T> =
        (Empty, array)
        ||> Array.fold (fun tree el ->
            insert el tree)

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


/// Additional AVL tree operations needed to implement the DIET.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private AvlDiet =
    open System.Collections.Generic
    open LanguagePrimitives

    //
    let [<Literal>] balanceTolerance = 1u

    /// Join two trees together at a pivot point, then balance the resulting tree.
    let private balance x l (r : AvlTree<'T>) =
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
    let reroot l (r : AvlTree<'T>) =
        if AvlTree.height l > AvlTree.height r then
            let i, l' = AvlTree.extractMax l
            join i l' r
        else
            if AvlTree.isEmpty r then Empty
            else
                let i, r' = AvlTree.extractMin r
                join i l r'


/// A Discrete Interval Encoding Tree (DIET) specialized to the 'char' type.
/// This is abbreviated in our documentation as a 'char-DIET'.
type private CharDiet = AvlTree<char * char>

/// Functional operations for char-DIETs.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private Diet =
    open System.Collections.Generic
    open LanguagePrimitives

    //
    let private charComparer =
        FastGenericComparer<char>

    //
    let inline pred (c : char) : char =
        char (int c - 1)
    
    //
    let inline succ (c : char) : char =
        char (int c + 1)

    //
    let inline dist (x : char) (y : char) : int =
        int y - int x

    //
    let inline private safe_pred (limit : char) (c : char) =
        if limit < c then
            char (int c - 1)
        else c

    //
    let inline private safe_succ (limit : char) (c : char) =
        if limit > c then
            char (int c + 1)
        else c

    //
    let inline height (t : CharDiet) =
        AvlTree.height t

    //
    let rec private find_del_left p (tree : CharDiet) =
        match tree with
        | AvlTree.Empty ->
            p, AvlTree.Empty
        | AvlTree.Node ((x, y), left, right, _) ->
            if compare p (succ y) > 0 then
                let p', right' = find_del_left p right
                p', AvlDiet.join (x, y) left right'
            elif compare p x < 0 then
                find_del_left p left
            else
                x, left

    //
    let rec private find_del_right p (tree : CharDiet) =
        match tree with
        | AvlTree.Empty ->
            p, AvlTree.Empty
        | AvlTree.Node ((x, y), left, right, _) ->
            if compare p (pred x) < 0 then
                let p', left' = find_del_right p left
                p', AvlDiet.join (x, y) left' right
            elif compare p y > 0 then
                find_del_right p right
            else
                y, right

    /// An empty DIET.
    let empty : CharDiet =
        AvlTree.empty

    /// Determines if a DIET is empty.
    let inline isEmpty (tree : CharDiet) =
        AvlTree.isEmpty tree

    /// Determines if a DIET contains a specified value.
    let rec contains value (tree : CharDiet) =
        match tree with
        | Empty ->
            false
        | Node ((x, y), left, right, _) ->
            if compare value x < 0 then
                contains value left
            elif compare value y > 0 then
                contains value right
            else true
        
    /// Gets the maximum (greatest) value stored in the DIET.
    let maxElement (tree : CharDiet) : char =
        snd <| AvlTree.maxElement tree
    
    /// Gets the minimum (least) value stored in the DIET.
    let minElement (tree : CharDiet) : char=
        fst <| AvlTree.minElement tree

    /// Creates a DIET containing the specified value.
    let singleton value : CharDiet =
        AvlTree.singleton <| (value, value)

    /// Creates a DIET containing the specified range of values.
    let ofRange minValue maxValue : CharDiet =
        // For compatibility with the F# range operator,
        // when minValue > minValue it's just considered
        // to be an empty range.
        if minValue >= maxValue then
            empty
        else
            AvlTree.singleton (minValue, maxValue)

    /// Returns the number of elements in the set.
    let count (t : CharDiet) =
        // OPTIMIZE : Modify this to use a mutable stack instead of an F# list.
        let rec cardinal_aux acc = function
            | [] -> acc
            | AvlTree.Empty :: ts ->
                cardinal_aux acc ts
            | AvlTree.Node ((x, y), left, right, _) :: ts ->
                let d = dist x y
                cardinal_aux (acc + d + 1) (left :: right :: ts)
        
        cardinal_aux 0 [t]

    /// Returns the number of intervals in the set.
    let intervalCount (t : CharDiet) =
        // OPTIMIZE : Modify this to use a mutable stack instead of an F# list.
        let rec cardinal_aux acc = function
            | [] -> acc
            | AvlTree.Empty :: ts ->
                cardinal_aux acc ts
            | AvlTree.Node (_, left, right, _) :: ts ->
                cardinal_aux (acc + 1) (left :: right :: ts)
        
        cardinal_aux 0 [t]

    /// Applies the given accumulating function to all elements in a DIET.
    let fold (folder : 'State -> char -> 'State) (state : 'State) (tree : CharDiet) =
        // Preconditions
        checkNonNull "tree" tree

        let folder = FSharpFunc<_,_,_>.Adapt folder

        let rangeFolder (state : 'State) (lo, hi) =
            // Fold over the items in increasing order.
            let mutable state = state
            for x = int lo to int hi do
                state <- folder.Invoke (state, char x)
            state

        AvlTree.fold rangeFolder state tree

    /// Applies the given accumulating function to all elements in a DIET.
    let foldBack (folder : char -> 'State -> 'State) (tree : CharDiet) (state : 'State) =
        // Preconditions
        checkNonNull "tree" tree

        let folder = FSharpFunc<_,_,_>.Adapt folder

        let rangeFolder (lo, hi) (state : 'State) =
            // Fold over the items in decreasing order.
            let mutable state = state
            for x = int hi downto int lo do
                state <- folder.Invoke (char x, state)
            state

        AvlTree.foldBack rangeFolder tree state

    /// Applies the given function to all elements in a DIET.
    let iter (action : char -> unit) (tree : CharDiet) =
        // Preconditions
        checkNonNull "tree" tree

        /// Applies the action to all values within an interval.
        let intervalApplicator (lo, hi) =
            for x = int lo to int hi do
                action (char x)

        AvlTree.iter intervalApplicator tree

    //
    let rec toSeq (tree : CharDiet) =
        seq {
        match tree with
        | Empty -> ()
        | Node ((x, y), l, r, _) ->
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

    //
    let forall (predicate : char -> bool) (t : CharDiet) =
        // OPTIMIZE : Rewrite this to short-circuit and return early
        // if we find a non-matching element.
        (true, t)
        ||> fold (fun state el ->
            state && predicate el)

    /// Returns a new set with the specified value added to the set.
    /// No exception is thrown if the set already contains the value.
    let rec add p (tree : CharDiet) : CharDiet =
        match tree with
        | Empty ->
            singleton p
        | Node ((x, y), left, right, h) as t ->
            if compare p x >= 0 then
                if compare p y <= 0 then t
                elif compare p (succ y) > 0 then
                    AvlDiet.join (x, y) left (add p right)
                elif AvlTree.isEmpty right then
                    AvlTree.Node ((x, p), left, right, h)
                else
                    let (u, v), r = AvlTree.extractMin right
                    if pred u = p then
                        AvlDiet.join (x, v) left r
                    else
                        AvlTree.Node ((x, p), left, right, h)

            elif compare p (pred x) < 0 then
                AvlDiet.join (x, y) (add p left) right
            elif AvlTree.isEmpty left then
                AvlTree.Node ((p, y), left, right, h)
            else
                let (u, v), l = AvlTree.extractMax left
                if (succ v) = p then
                    AvlDiet.join (u, y) l right
                else
                    AvlTree.Node ((p, y), left, right, h)

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

    /// Returns a new set with the specified range of values added to the set.
    /// No exception is thrown if any of the values are already contained in the set.
    let rec addRange (p, q) (tree : CharDiet) : CharDiet =
        match tree with
        | AvlTree.Empty ->
            AvlTree.singleton (p, q)
        | AvlTree.Node ((x, y), left, right, _) ->
            if compare q (pred x) < 0 then
                AvlDiet.join (x, y) (addRange (p, q) left) right
            elif compare p (succ y) > 0 then
                AvlDiet.join (x, y) left (addRange (p, q) right)
            else
                let x', left' =
                    if compare p x >= 0 then x, left
                    else find_del_left p left
                let y', right' =
                    if compare q y <= 0 then y, right
                    else find_del_right q right

                AvlDiet.join (x', y') left' right'

    /// Returns a new set with the given element removed.
    /// No exception is thrown if the set doesn't contain the specified element.
    let rec remove z (tree : CharDiet) : CharDiet =
        match tree with
        | AvlTree.Empty ->
            AvlTree.Empty
        | AvlTree.Node ((x, y), left, right, h) ->
            let czx = compare z x
            if czx < 0 then
                AvlDiet.join (x, y) (remove z left) right
            else
                let cyz = compare y z
                if cyz < 0 then
                    AvlDiet.join (x, y) left (remove z right)
                elif cyz = 0 then
                    if czx = 0 then
                        AvlDiet.reroot left right
                    else
                        AvlTree.Node ((x, pred y), left, right, h)
                elif czx = 0 then
                    AvlTree.Node ((succ x, y), left, right, h)
                else
                    addRange (succ z, y) (AvlTree.Node ((x, pred z), left, right, h))

    let rec private union_helper left (a, b) right limit head stream =        
        match head with
        | None ->
            AvlDiet.join (a,b) left right, None, AvlTree.Empty
        | Some (x, y) ->
            let greater_limit z =
                match limit with
                | None -> false
                | Some u ->
                    compare z u >= 0
                
            if compare y a < 0 && compare y (pred a) < 0 then
                let left' = addRange (x, y) left
                let head, stream = AvlTree.tryExtractMin stream
                union_helper left' (a, b) right limit head stream

            elif compare x b > 0 && compare x (succ b) > 0 then
                let right', head, stream = union' right limit head stream
                AvlDiet.join (a,b) left right', head, stream

            elif compare b y >= 0 then
                let head, stream = AvlTree.tryExtractMin stream
                union_helper left (min a x, b) right limit head stream

            elif greater_limit y then
                left, Some (min a x, y), stream

            else
                let right', head, stream = union' right limit (Some (min a x, y)) stream
                AvlDiet.reroot left right', head, stream

    and private union' (input : CharDiet) limit head (stream : CharDiet) =
        match head with
        | None ->
            input, None, AvlTree.Empty
        | Some (x, y) ->
            match input with
            | AvlTree.Empty ->
                AvlTree.Empty, head, stream
            | AvlTree.Node ((a, b), left, right, _) ->
                let left', head, stream =
                    if compare x a < 0 then
                        union' left (Some <| pred a) head stream
                    else
                        left, head, stream
                union_helper left' (a, b) right limit head stream

    /// Computes the union of the two sets.
    let rec union (input : CharDiet) (stream : CharDiet) : CharDiet =
        if AvlTree.height stream > AvlTree.height input then
            union stream input
        else
            #if DEBUG
            /// The minimum possible number of elements in the resulting set.
            let minPossibleResultCount =
                let inputCount = count input
                let streamCount = count stream
                GenericMaximum inputCount streamCount
            #endif

            let head, stream' =
                AvlTree.tryExtractMin stream

            let result, head', stream'' =
                union' input None head stream'
            let result =
                match head' with
                | None ->
                    result
                | Some i ->
                    AvlDiet.join i result stream''

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
            #endif
            result

    /// Computes the intersection of the two sets.
    let rec intersect (input : CharDiet) (stream : CharDiet) : CharDiet =
        let rec inter' (input : CharDiet) head (stream : CharDiet) =
            match head with
            | None ->
                AvlTree.Empty, None, AvlTree.Empty
            | Some (x, y) ->
                match input with
                | AvlTree.Empty ->
                    AvlTree.Empty, head, stream
                | AvlTree.Node ((a, b), left, right, _) ->
                    let left, head, stream =
                        if compare x a < 0 then
                            inter' left head stream
                        else
                            AvlTree.Empty, head, stream

                    inter_help (a, b) right left head stream

        and inter_help (a, b) (right : CharDiet) (left : CharDiet) head stream =
            match head with
            | None ->
                left, None, AvlTree.Empty
            | Some (x, y) ->
                if compare y a < 0 then
                    if AvlTree.isEmpty stream then
                        (left, None, AvlTree.Empty)
                    else
                        let head, stream = AvlTree.extractMin stream
                        inter_help (a, b) right left (Some head) stream
                elif compare b x < 0 then
                    let right, head, stream = inter' right head stream
                    AvlDiet.reroot left right, head, stream
                elif compare y (safe_pred y b) >= 0 then
                    let right, head, stream = inter' right head stream
                    (AvlDiet.join (max x a, min y b) left right), head, stream
                else
                    let left = addRange (max x a, y) left
                    inter_help (succ y, b) right left head stream

        if AvlTree.height stream > AvlTree.height input then
            intersect stream input
        elif AvlTree.isEmpty stream then
            AvlTree.Empty
        else
            let head, stream = AvlTree.extractMin stream
            let result, _, _ = inter' input (Some head) stream
            result

    /// Returns a new set with the elements of the second set removed from the first.
    let difference (input : CharDiet) (stream : CharDiet) : CharDiet =
        let rec diff' input head stream =
            match head with
            | None ->
                input, None, AvlTree.Empty
            | Some (x, y) ->
                match input with
                | AvlTree.Empty ->
                    AvlTree.Empty, head, stream
                | AvlTree.Node ((a, b), left, right, _) ->
                    let left, head, stream =
                        if compare x a < 0 then
                            diff' left head stream
                        else
                            left, head, stream
                    diff_helper (a, b) right left head stream

        and diff_helper (a, b) (right : CharDiet) (left : CharDiet) head stream =
            match head with
            | None ->
                AvlDiet.join (a, b) left right, None, AvlTree.Empty
            | Some (x, y) ->
                if compare y a < 0 then
                    // [x, y] and [a, b] are disjoint
                    let head, stream = AvlTree.tryExtractMin stream
                    diff_helper (a, b) right left head stream
                elif compare b x < 0 then
                    // [a, b] and [x, y] are disjoint
                    let right, head, stream = diff' right head stream
                    AvlDiet.join (a, b) left right, head, stream
                elif compare a x < 0 then
                    // [a, b] and [x, y] overlap
                    // a < x
                    diff_helper (x, b) right ((addRange (a, pred x) left)) head stream
                elif compare y b < 0 then
                    // [a, b] and [x, y] overlap
                    // y < b
                    let head, stream = AvlTree.tryExtractMin stream
                    diff_helper (succ y, b) right left head stream
                else
                    // [a, b] and [x, y] overlap
                    let right, head, stream = diff' right head stream
                    AvlDiet.reroot left right, head, stream
        
        if AvlTree.isEmpty stream then
            input
        else
            #if DEBUG
            /// The minimum possible number of elements in the resulting set.
            let minPossibleResultCount =
                let inputCount = count input
                let streamCount = count stream
                GenericMaximum 0 (inputCount - streamCount)
            #endif

            let head, stream' = AvlTree.extractMin stream
            let result, _, _ = diff' input (Some head) stream'

            #if DEBUG
            let resultCount = count result
            Debug.Assert (
                resultCount >= minPossibleResultCount,
                sprintf "The result set should not contain fewer than %i elements, but it contains only %i elements."
                    minPossibleResultCount resultCount)
            #endif

            result

    /// Comparison function for DIETs.
    let rec comparison (t1 : CharDiet) (t2 : CharDiet) =
        match t1, t2 with
        | Node (_,_,_,_), Node (_,_,_,_) ->
            let (ix1, iy1), r1 = AvlTree.extractMin t1
            let (ix2, iy2), r2 = AvlTree.extractMin t2
            let c =
                let d = compare ix1 ix2
                if d <> 0 then -d
                else compare iy1 iy2
            if c <> 0 then c
            else comparison r1 r2
        
        | Node (_,_,_,_), Empty -> 1
        | Empty, Empty -> 0
        | Empty, Node (_,_,_,_) -> -1

    /// Equality function for DIETs.
    let equal (t1 : CharDiet) (t2 : CharDiet) =
        comparison t1 t2 = 0

    //
    let rec split x (tree : CharDiet) =
        match tree with
        | AvlTree.Empty ->
            AvlTree.Empty, false, AvlTree.Empty
        | AvlTree.Node ((a, b), l, r, _) ->
            let cxa = compare x a
            if cxa < 0 then
                let ll, pres, rl = split x l
                ll, pres, AvlDiet.join (a, b) rl r
            else
                let cbx = compare b x
                if cbx < 0 then
                    let lr, pres, rr = split x r
                    AvlDiet.join (a, b) l lr, pres, rr
                else
                    (if cxa = 0 then l else addRange (a, pred x) l),
                    true,
                    (if cbx = 0 then r else addRange (succ x, b) r)


/// Character set implementation based on a Discrete Interval Encoding Tree.
/// This is faster and more efficient than the built-in F# Set<'T>,
/// especially for dense sets.
[<DebuggerDisplay("Count = {Count}, Intervals = {IntervalCount}")>]
type CharSet private (dietSet : CharDiet) =
    //
    static let empty = CharSet (Diet.empty)

    //
    static let charComparer =
        LanguagePrimitives.FastGenericComparer<char>

    //
    static member Empty
        with get () = empty
    
    override __.GetHashCode () =
        // TODO : Come up with a better hashcode function.
        (Diet.count dietSet) * (int <| AvlTree.height dietSet)
    
    override __.Equals other =
        match other with
        | :? CharSet as other ->
            Diet.equal dietSet other.DietSet
        | _ ->
            false

    //
    member private __.DietSet
        with get () = dietSet

    //
    member __.Count
        with get () =
            Diet.count dietSet

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
        CharSet (Diet.add value charSet.DietSet)

    //
    static member AddRange (lower, upper, charSet : CharSet) =
        CharSet (Diet.addRange (lower, upper) charSet.DietSet)

    //
    static member Remove (value, charSet : CharSet) =
        CharSet (Diet.remove value charSet.DietSet)

    //
    static member Contains (value, charSet : CharSet) =
        Diet.contains value charSet.DietSet

//    //
//    static member ToList (charSet : CharSet) =
//        Diet.toList charSet.DietSet

    //
    static member OfList list =
        CharSet (Diet.ofList list)

//    //
//    static member ToSet (charSet : CharSet) =
//        Diet.toSet charSet.DietSet

//    //
//    static member OfSet set =
//        CharSet (Diet.ofSet set)

//    //
//    static member ToArray (charSet : CharSet) =
//        Diet.toArray charSet.DietSet
    
    //
    static member OfArray array =
        CharSet (Diet.ofArray array)

//    //
//    static member ToSequence (charSet : CharSet) =
//        Diet.toSeq charSet.DietSet

    //
    static member OfSequence sequence =
        CharSet (Diet.ofSeq sequence)

    //
    static member Difference (charSet1 : CharSet, charSet2 : CharSet) =
        CharSet (Diet.difference charSet1.DietSet charSet2.DietSet)

    //
    static member Intersect (charSet1 : CharSet, charSet2 : CharSet) =
        CharSet (Diet.intersect charSet1.DietSet charSet2.DietSet)

    //
    static member Union (charSet1 : CharSet, charSet2 : CharSet) =
        CharSet (Diet.union charSet1.DietSet charSet2.DietSet)

    //
    static member Fold (folder : 'State -> _ -> 'State, state, charSet : CharSet) =
        Diet.fold folder state charSet.DietSet

    //
    static member FoldBack (folder : _ -> 'State -> 'State, state, charSet : CharSet) =
        Diet.foldBack folder charSet.DietSet state

    //
    static member Forall (predicate, charSet : CharSet) =
        Diet.forall predicate charSet.DietSet

    //
    static member IterateIntervals (action, charSet : CharSet) =
        let action = FSharpFunc<_,_,_>.Adapt action
        charSet.DietSet
        |> AvlTree.iter action.Invoke

    interface System.IComparable with
        member this.CompareTo other =
            match other with
            | :? CharSet as other ->
                Diet.comparison this.DietSet other.DietSet
            | _ ->
                invalidArg "other" "The argument is not an instance of CharSet."

    interface System.IComparable<CharSet> with
        member this.CompareTo other =
            Diet.comparison dietSet other.DietSet

    interface System.IEquatable<CharSet> with
        member this.Equals other =
            Diet.equal dietSet other.DietSet


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


