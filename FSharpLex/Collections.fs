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

//
namespace FSharpLex.SpecializedCollections

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
            (e.g., 'fold', 'iter') were implemented.
            
            The DIET code was ported from Friedmann and Lange's 'camldiets' code, which is
            based on their paper "More on Balanced Diets". Their code was adapted to F# and
            the AVL tree extracted from Isabelle/HOL, then specialized for the 'char' type. *)

(*
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
    let empty : AvlTree<'T> = Empty

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
    let inline private pred (c : char) : char =
        char (int c - 1)
    
    //
    let inline private succ (c : char) : char =
        char (int c + 1)

    //
    let inline private dist (x : char) (y : char) : int =
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
        | Empty ->
            p, Empty
        | Node ((x, y), left, right, _) ->
            if p > succ y then
                let p', right' = find_del_left p right
                p', AvlDiet.join (x, y) left right'
            elif p < x then
                find_del_left p left
            else
                x, left

    //
    let rec private find_del_right p (tree : CharDiet) =
        match tree with
        | Empty ->
            p, Empty
        | Node ((x, y), left, right, _) ->
            if p < pred x then
                let p', left' = find_del_right p left
                p', AvlDiet.join (x, y) left' right
            elif p > y then
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
            snd <| AvlTree.maxElement tree
    
    /// Gets the minimum (least) value stored in the DIET.
    let minElement (tree : CharDiet) : char =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | tree ->
            fst <| AvlTree.minElement tree

    /// Gets the minimum (least) and maximum (greatest) values store in the DIET.
    let bounds (tree : CharDiet) : char * char =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | tree ->
            minElement tree, maxElement tree

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
            | Empty :: ts ->
                cardinal_aux acc ts
            | Node ((x, y), left, right, _) :: ts ->
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
            | Node (_, left, right, _) :: ts ->
                cardinal_aux (acc + 1) (left :: right :: ts)
        
        cardinal_aux 0 [t]

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

        AvlTree.fold rangeFolder state tree

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

        AvlTree.foldBack rangeFolder tree state

    /// Applies the given function to all elements in a DIET.
    let iter (action : char -> unit) (tree : CharDiet) =
        // Preconditions
        // NONE -- Skip null check because the Empty tree is represented as null.

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
    let rec add value (tree : CharDiet) : CharDiet =
        match tree with
        | Empty ->
            singleton value
        | Node ((x, y), left, right, h) as t ->
            if value >= x then
                if value <= y then t
                elif value > succ y then
                    AvlDiet.join (x, y) left (add value right)
                elif AvlTree.isEmpty right then
                    Node ((x, value), left, right, h)
                else
                    let (u, v), r = AvlTree.extractMin right
                    if pred u = value then
                        AvlDiet.join (x, v) left r
                    else
                        Node ((x, value), left, right, h)

            elif value < pred x then
                AvlDiet.join (x, y) (add value left) right
            elif AvlTree.isEmpty left then
                Node ((value, y), left, right, h)
            else
                let (u, v), l = AvlTree.extractMax left
                if succ v = value then
                    AvlDiet.join (u, y) l right
                else
                    Node ((value, y), left, right, h)

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
        | Empty ->
            AvlTree.singleton (p, q)
        | Node ((x, y), left, right, _) ->
            if q < pred x then
                AvlDiet.join (x, y) (addRange (p, q) left) right
            elif p > succ y then
                AvlDiet.join (x, y) left (addRange (p, q) right)
            else
                let x', left' =
                    if p >= x then x, left
                    else find_del_left p left
                let y', right' =
                    if q <= y then y, right
                    else find_del_right q right

                AvlDiet.join (x', y') left' right'

    /// Returns a new set with the given element removed.
    /// No exception is thrown if the set doesn't contain the specified element.
    let rec remove value (tree : CharDiet) : CharDiet =
        match tree with
        | Empty ->
            Empty
        | Node ((x, y), left, right, h) ->
            let czx = compare value x
            if czx < 0 then
                AvlDiet.join (x, y) (remove value left) right
            else
                let cyz = compare y value
                if cyz < 0 then
                    AvlDiet.join (x, y) left (remove value right)
                elif cyz = 0 then
                    if czx = 0 then
                        AvlDiet.reroot left right
                    else
                        Node ((x, pred y), left, right, h)
                elif czx = 0 then
                    Node ((succ x, y), left, right, h)
                else
                    addRange (succ value, y) (Node ((x, pred value), left, right, h))    

    /// Computes the union of the two sets.
    let rec union (input : CharDiet) (stream : CharDiet) : CharDiet =
        let rec union' (input : CharDiet) limit head (stream : CharDiet) =
            match head with
            | None ->
                input, None, Empty
            | Some (x, y) ->
                match input with
                | Empty ->
                    Empty, head, stream
                | Node ((a, b), left, right, _) ->
                    let left', head, stream =
                        if x < a then
                            union' left (Some <| pred a) head stream
                        else
                            left, head, stream
                    union_helper left' (a, b) right limit head stream

        and union_helper left (a, b) right limit head stream =
            match head with
            | None ->
                AvlDiet.join (a, b) left right, None, Empty
            | Some (x, y) ->
                let greater_limit z =
                    match limit with
                    | None -> false
                    | Some u ->
                        z >= u

                if y < a && y < pred a then
                    let left' = addRange (x, y) left
                    let head, stream = AvlTree.tryExtractMin stream
                    union_helper left' (a, b) right limit head stream

                elif x > b && x > succ b then
                    let right', head, stream = union' right limit head stream
                    AvlDiet.join (a,b) left right', head, stream

                elif b >= y then
                    let head, stream = AvlTree.tryExtractMin stream
                    union_helper left (min a x, b) right limit head stream

                elif greater_limit y then
                    left, Some (min a x, y), stream

                else
                    let right', head, stream = union' right limit (Some (min a x, y)) stream
                    AvlDiet.reroot left right', head, stream

        if AvlTree.height stream > AvlTree.height input then
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

            let result =
                let result, head', stream'' =
                    let head, stream' = AvlTree.tryExtractMin stream
                    union' input None head stream'

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
            Debug.Assert (
                resultCount <= maxPossibleResultCount,
                sprintf "The result set should not contain more than %i elements, but it contains %i elements."
                    maxPossibleResultCount resultCount)
            #endif
            result

    /// Computes the intersection of the two sets.
    let rec intersect (input : CharDiet) (stream : CharDiet) : CharDiet =
        let rec inter' (input : CharDiet) head (stream : CharDiet) =
            match head with
            | None ->
                Empty, None, Empty
            | Some (x, y) ->
                match input with
                | Empty ->
                    Empty, head, stream
                | Node ((a, b), left, right, _) ->
                    let left, head, stream =
                        if x < a then
                            inter' left head stream
                        else
                            Empty, head, stream

                    inter_help (a, b) right left head stream

        and inter_help (a, b) (right : CharDiet) (left : CharDiet) head stream =
            match head with
            | None ->
                left, None, Empty
            | Some (x, y) ->
                if y < a then
                    if AvlTree.isEmpty stream then
                        (left, None, Empty)
                    else
                        let head, stream = AvlTree.extractMin stream
                        inter_help (a, b) right left (Some head) stream
                elif b < x then
                    let right, head, stream = inter' right head stream
                    AvlDiet.reroot left right, head, stream
                elif y >= safe_pred y b then
                    let right, head, stream = inter' right head stream
                    (AvlDiet.join (max x a, min y b) left right), head, stream
                else
                    let left = addRange (max x a, y) left
                    inter_help (succ y, b) right left head stream

        if AvlTree.height stream > AvlTree.height input then
            intersect stream input
        elif AvlTree.isEmpty stream then
            Empty
        else
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
                let head, stream = AvlTree.extractMin stream
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

    /// Returns a new set with the elements of the second set removed from the first.
    let difference (input : CharDiet) (stream : CharDiet) : CharDiet =
        let rec diff' input head stream =
            match head with
            | None ->
                input, None, Empty
            | Some (x, y) ->
                match input with
                | Empty ->
                    Empty, head, stream
                | Node ((a, b), left, right, _) ->
                    let left, head, stream =
                        if x < a then
                            diff' left head stream
                        else
                            left, head, stream
                    diff_helper (a, b) right left head stream

        and diff_helper (a, b) (right : CharDiet) (left : CharDiet) head stream =
            match head with
            | None ->
                AvlDiet.join (a, b) left right, None, Empty
            | Some (x, y) ->
                if y < a then
                    // [x, y] and [a, b] are disjoint
                    let head, stream = AvlTree.tryExtractMin stream
                    diff_helper (a, b) right left head stream
                elif b < x then
                    // [a, b] and [x, y] are disjoint
                    let right, head, stream = diff' right head stream
                    AvlDiet.join (a, b) left right, head, stream
                elif a < x then
                    // [a, b] and [x, y] overlap
                    // a < x
                    diff_helper (x, b) right ((addRange (a, pred x) left)) head stream
                elif y < b then
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
    let rec split x (tree : CharDiet) : CharDiet * bool * CharDiet =
        match tree with
        | Empty ->
            Empty, false, Empty
        | Node ((a, b), l, r, _) ->
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
*)

/// Character set implementation based on a Discrete Interval Encoding Tree.
/// This is faster and more efficient than the built-in F# Set<'T>,
/// especially for dense sets.
[<DebuggerDisplay(
    "Count = {DebuggerElementCount}, \
     Intervals = {DebuggerIntervalCount}")>]
type CharSet =
    | Empty
    | Node of char * char * CharSet * CharSet

    //
    member private this.DebuggerElementCount
        with get () =
            CharSet.Count this

    //
    member private this.DebuggerIntervalCount
        with get () =
            CharSet.IntervalCount this

    //
    static member private CountImpl tree cont =
        match tree with
        | Empty ->
            cont 0
        | Node (lowerBound, upperBound, left, right) ->
            // Count the left and right subtrees.
            CharSet.CountImpl left <| fun leftCount ->
            CharSet.CountImpl right <| fun rightCount ->
                /// The number of values in this interval.
                let thisCount = int upperBound - int lowerBound + 1

                // Return the combined count for this node and it's children.
                thisCount + leftCount + rightCount
                |> cont

    /// Returns the number of elements in the set.
    static member Count tree =
        CharSet.CountImpl tree id

    //
    static member private IntervalCountImpl tree cont =
        match tree with
        | Empty ->
            cont 0
        | Node (lowerBound, upperBound, left, right) ->
            // Count the left and right subtrees.
            CharSet.IntervalCountImpl left <| fun leftCount ->
            CharSet.IntervalCountImpl right <| fun rightCount ->
                // Combine the interval count for this node's children, then increment it.
                1 + leftCount + rightCount
                |> cont

    /// Returns the number of intervals in the set.
    static member IntervalCount tree =
        CharSet.IntervalCountImpl tree id

    /// The set containing the given element.
    static member FromElement value =
        Node (value, value, Empty, Empty)

    /// The set containing the elements in the given range.
    static member FromRange (lowerBound, upperBound) =
        // For compatibility with the F# range operator,
        // when lowerBound > upperBound it's just considered
        // to be an empty range.
        if lowerBound >= upperBound then
            Empty
        else
            Node (lowerBound, upperBound, Empty, Empty)

/// Functional programming operators related to the CharSet type.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module CharSet =
    /// The empty set.
    let empty = CharSet.Empty

    /// Returns 'true' if the set is empty.
    [<CompiledName("IsEmpty")>]
    let isEmpty set =
        match set with
        | Empty -> true
        | Node (_,_,_,_) -> false

    /// The set containing the given element.
    [<CompiledName("FromElement")>]
    let inline singleton c =
        CharSet.FromElement c

    /// The set containing the elements in the given range.
    [<CompiledName("FromRange")>]
    let inline ofRange lowerBound upperBound =
        CharSet.FromRange (lowerBound, upperBound)

    /// Returns the number of elements in the set.
    [<CompiledName("Count")>]
    let inline count (set : CharSet) =
        CharSet.Count set

    /// Returns the number of intervals in the set.
    [<CompiledName("IntervalCount")>]
    let inline intervalCount (set : CharSet) =
        CharSet.IntervalCount set

    //
    let rec private splitMaxImpl tree cont =
        match tree with
        | Empty ->
            invalidArg "tree" "Cannot split an empty tree."
        | Node (x, y, l, Empty) ->
            cont (x, y, l)
        | Node (x, y, l, r) ->
            splitMaxImpl r <| fun (u, v, r') ->
                cont (u, v, Node (x, y, l, r'))

    //
    let private splitMax tree =
        splitMaxImpl tree id

    //
    let rec private splitMinImpl tree cont =
        match tree with
        | Empty ->
            invalidArg "tree" "Cannot split an empty tree."
        | Node (x, y, Empty, r) ->
            cont (x, y, r)
        | Node (x, y, l, r) ->
            splitMinImpl l <| fun (u, v, l') ->
                cont (u, v, Node (x, y, l', r))

    //
    let private splitMin tree =
        splitMinImpl tree id

    //
    let private joinLeft = function
        | Empty ->
            invalidArg "tree" "Cannot join an empty tree."
        | Node (x, y, Empty, r) as t -> t
        | Node (x, y, l, r) ->
            let x', y', l' = splitMax l
            if y' + (char 1) = x then
                Node (x', y, l', r)
            else
                Node (x, y, l, r)

    //
    let private joinRight = function
        | Empty ->
            invalidArg "tree" "Cannot join an empty tree."
        | Node (x, y, l, Empty) as t -> t
        | Node (x, y, l, r) ->
            let x', y', r' = splitMin r
            if y + (char 1) = x' then
                Node (x, y', l, r')
            else
                Node (x, y, l, r)

    //
    let rec private addImpl value tree cont =
        match tree with
        | Empty ->
            Node (value, value, Empty, Empty)
            |> cont
        | Node (x, y, l, r) as t ->
            if value < x then
                if value + (char 1) = x then
                    Node (value, y, l, r)
                    |> joinLeft
                    |> cont
                else
                    addImpl value l <| fun l ->
                        Node (x, y, l, r)
                        |> cont
            elif value > y then
                if value = y + (char 1) then
                    Node (x, value, l, r)
                    |> joinRight
                    |> cont
                else
                    addImpl value r <| fun r ->
                        Node (x, y, l, r)
                        |> cont
            else
                cont t (* value in [x, y] *)

    /// Returns a new set with an element added to the set.
    /// No exception is raised if the set already contains the given element.
    [<CompiledName("Add")>]
    let add value tree =
        addImpl value tree id

    //
    let private merge = function
        | l, Empty -> l
        | Empty, r -> r
        | l, r ->
            let x, y, l' = splitMax l
            Node (x, y, l', r)

    //
    [<CompiledName("AddRange")>]
    let addRange lower upper tree =
        // If the range is "inverted", we consider the range
        // to be empty and simply return the original tree.
        if lower > upper then tree
        else
            // If the input set is empty, optimize by immediately
            // creating a new set from the specified range.
            match tree with
            | Empty ->
                Node (lower, upper, Empty, Empty)
            | Node (_,_,_,_) as tree ->
                // OPTIMIZE : Implement some function which adds the values into
                // the tree symbolically -- it'll be *way* faster.
                (tree, seq { lower .. upper })
                ||> Seq.fold (fun tree el ->
                    add el tree)

    //
    let rec private removeImpl value tree cont =
        match tree with
        | Empty ->
            cont Empty
        | Node (x, y, l, r) ->
            if value < x then
                removeImpl value l <| fun l ->
                    Node (x, y, l, r)
                    |> cont
            elif value > y then
                removeImpl value r <| fun r ->
                    Node (x, y, l, r)
                    |> cont
            elif value = x then
                if x = y then
                    // node must be removed
                    merge (l, r)
                    |> cont
                else
                    // interval can be simply shrunk
                    Node (x + (char 1), y, l, r)
                    |> cont
            elif value = y then
                // since value<>x => y>x
                Node (x, (char (int y - 1)), l, r)
                |> cont
            else
                // split interval
                Node (x, (char (int value - 1)), l, Node (value + (char 1), y, Empty, r))
                |> cont

    /// Returns a new set with the given element removed.
    /// No exception is raised if the set doesn't contain the given element.
    [<CompiledName("Remove")>]
    let remove value tree =
        removeImpl value tree id

    /// Evaluates to 'true' if the given element is in the given set.
    [<CompiledName("Contains")>]
    let rec contains value tree =
        match tree with
        | Empty ->
            false
        | Node (y, z, l, r) ->
            if value >= y && value <= z then true
            elif value < y then
                contains value l
            else
                // value > z
                contains value r

    //
    let rec private foldImpl (folder : FSharpFunc<'State, char, 'State>) (state : 'State) tree cont =
        match tree with
        | Empty ->
            cont state
        | Node (lowerBound, upperBound, left, right) ->
            // Fold over the left subtree
            foldImpl folder state left <| fun state ->
                // Fold over the values in this interval.
                let mutable state = state
                let lowerBound = int lowerBound
                let upperBound = int upperBound
                for i = lowerBound to upperBound do
                    state <- folder.Invoke (state, char i)

                // Fold over the right subtree
                foldImpl folder state right cont

    /// Applies the given accumulating function to all the elements of the set.
    [<CompiledName("Fold")>]
    let fold (folder : 'State -> char -> 'State) (state : 'State) tree =
        let folder = FSharpFunc<_,_,_>.Adapt folder
        foldImpl folder state tree id

    //
    let rec private foldBackImpl (folder : FSharpFunc<char, 'State, 'State>) tree (state : 'State) cont =
        match tree with
        | Empty ->
            cont state
        | Node (lowerBound, upperBound, left, right) ->
            // Fold backward over the right subtree
            foldBackImpl folder right state <| fun state ->

            // Fold downward over the values in this interval
            let mutable state = state
            let upperBound = int upperBound
            let lowerBound = int lowerBound
            for i = upperBound downto lowerBound do
                state <- folder.Invoke (char i, state)

            // Fold backward over the left subtree
            foldBackImpl folder left state cont

    /// Applies the given accumulating function to all the elements of the set.
    [<CompiledName("FoldBack")>]
    let foldBack (folder : char -> 'State -> 'State) tree (state : 'State) =
        let folder = FSharpFunc<_,_,_>.Adapt folder
        foldBackImpl folder tree state id

    //
    let rec private foldIntervalsImpl (folder : FSharpFunc<'State, char, char, 'State>) (state : 'State) tree cont =
        match tree with
        | Empty ->
            cont state
        | Node (lowerBound, upperBound, left, right) ->
            // Fold over the left subtree
            foldIntervalsImpl folder state left <| fun state ->
                // Apply the folder function to this interval.
                let state = folder.Invoke (state, lowerBound, upperBound)

                // Fold over the right subtree
                foldIntervalsImpl folder state right cont

    /// Applies the given accumulating function to all the intervals of the set.
    [<CompiledName("FoldIntervals")>]
    let foldIntervals (folder : 'State -> char -> char -> 'State) (state : 'State) tree =
        let folder = FSharpFunc<_,_,_,_>.Adapt folder
        foldIntervalsImpl folder state tree id

    //
    let rec private foldBackIntervalsImpl (folder : FSharpFunc<char, char, 'State, 'State>) tree (state : 'State) cont =
        match tree with
        | Empty ->
            cont state
        | Node (lowerBound, upperBound, left, right) ->
            // Fold backward over the right subtree
            foldBackIntervalsImpl folder right state <| fun state ->

            // Apply the folder function to this interval.
            let state = folder.Invoke (lowerBound, upperBound, state)

            // Fold backward over the left subtree
            foldBackIntervalsImpl folder left state cont

    /// Applies the given accumulating function to all the elements of the set.
    [<CompiledName("FoldBackIntervals")>]
    let foldBackIntervals (folder : char -> char -> 'State -> 'State) tree (state : 'State) =
        let folder = FSharpFunc<_,_,_,_>.Adapt folder
        foldBackIntervalsImpl folder tree state id

    /// Returns a new set containing the results of applying the given function to each element of the input set.
    [<CompiledName("Map")>]
    let map (mapping : char -> char) tree =
        (empty, tree)
        ||> fold (fun set el ->
            add (mapping el) set)

    /// Returns a new set containing only the elements of the collection for which the given predicate returns true.
    [<CompiledName("Filter")>]
    let filter (predicate : char -> bool) tree =
        (empty, tree)
        ||> fold (fun set el ->
            if predicate el then
                add el set
            else set)

    //
    let rec private iterImpl (action : char -> unit) tree cont =
        match tree with
        | Empty ->
            cont ()
        | Node (lowerBound, upperBound, left, right) ->
            // Iterate over the left subtree
            iterImpl action left <| fun () ->

            // Iterate over the values in this interval
            let lowerBound = int lowerBound
            let upperBound = int upperBound
            for i = lowerBound to upperBound do
                action (char i)

            // Iterate over the right subtree
            iterImpl action right cont

    /// Applies the given function to each element of the set, in order from least to greatest.
    [<CompiledName("Iterate")>]
    let iter (action : char -> unit) tree =
        iterImpl action tree id

    //
    let rec private iterIntervalsImpl (action : FSharpFunc<char, char, unit>) tree cont =
        match tree with
        | Empty ->
            cont ()
        | Node (lowerBound, upperBound, left, right) ->
            // Iterate over the left subtree
            iterIntervalsImpl action left <| fun () ->

            // Apply this interval to the action.
            action.Invoke (lowerBound, upperBound)

            // Iterate over the right subtree
            iterIntervalsImpl action right cont

    /// Applies the given function to each element of the set, in order from least to greatest.
    [<CompiledName("IterateIntervals")>]
    let iterIntervals (action : char -> char -> unit) tree =
        let action = FSharpFunc<_,_,_>.Adapt action
        iterIntervalsImpl action tree id

    //
    let rec private existsImpl (predicate : char -> bool) tree cont =
        match tree with
        | Empty ->
            cont false
        | Node (lowerBound, upperBound, left, right) ->
            // Check the left subtree
            existsImpl predicate left <| fun leftResult ->
                if leftResult then
                    cont true
                else
                    // Check the current interval
                    let mutable result = false
                    let mutable i = lowerBound
                    while i <= upperBound && not result do
                        result <- predicate i
                        i <- i + (char 1)

                    if result then
                        cont true
                    else
                        // Check the right subtree
                        existsImpl predicate right cont

    /// Tests if any element of the collection satisfies the given predicate.
    /// If the input function is <c>predicate</c> and the elements are <c>i0...iN</c>,
    /// then this function computes predicate <c>i0 or ... or predicate iN</c>.
    [<CompiledName("Exists")>]
    let exists (predicate : char -> bool) tree =
        existsImpl predicate tree id

    //
    let rec private forallImpl (predicate : char -> bool) tree cont =
        match tree with
        | Empty ->
            cont true
        | Node (lowerBound, upperBound, left, right) ->
            // Check the left subtree
            forallImpl predicate left <| fun leftResult ->
                if not leftResult then
                    cont false
                else
                    // Check the current interval
                    let mutable result = true
                    let mutable i = lowerBound
                    while i <= upperBound && result do
                        result <- predicate i
                        i <- i + (char 1)

                    if not result then
                        cont false
                    else
                        // Check the right subtree
                        forallImpl predicate right cont

    /// Tests if all elements of the collection satisfy the given predicate.
    /// If the input function is <c>p</c> and the elements are <c>i0...iN</c>,
    /// then this function computes <c>p i0 && ... && p iN</c>.
    [<CompiledName("Forall")>]
    let forall (predicate : char -> bool) tree =
        forallImpl predicate tree id

    /// Creates a list that contains the elements of the set in order.
    [<CompiledName("ToList")>]
    let toList tree =
        // Fold backwards so we don't need to reverse the list.
        (tree, [])
        ||> foldBack (fun i lst ->
            i :: lst)

    /// Creates a set that contains the same elements as the given list.
    [<CompiledName("OfList")>]
    let ofList list =
        (empty, list)
        ||> List.fold (fun tree el ->
            add el tree)

    /// Creates a Set that contains the same elements as the given CharSet.
    [<CompiledName("ToSet")>]
    let toSet tree =
        (Set.empty, tree)
        ||> fold (fun set el ->
            Set.add el set)

    /// Creates a CharSet that contains the same elements as the given Set.
    [<CompiledName("OfSet")>]
    let ofSet set =
        (empty, set)
        ||> Set.fold (fun tree el ->
            add el tree)

    /// Creates an array that contains the elements of the set in order.
    [<CompiledName("ToArray")>]
    let toArray tree =
        let resizeArr = ResizeArray<_> ()
        iter resizeArr.Add tree
        resizeArr.ToArray ()

    /// Creates a set that contains the same elements as the given array.
    [<CompiledName("OfArray")>]
    let ofArray array =
        (empty, array)
        ||> Array.fold (fun tree el ->
            add el tree)

    /// Returns an ordered view of the set as an enumerable object.
    [<CompiledName("ToSeq")>]
    let rec toSeq tree =
        seq {
        match tree with
        | Empty -> ()
        | Node (lowerBound, upperBound, left, right) ->
            // Produce the sequence for the left subtree.
            yield! toSeq left

            // Produce the sequence of values in this interval.
            yield! { lowerBound .. upperBound }

            // Produce the sequence for the right subtree.
            yield! toSeq right }

    /// Creates a new set from the given enumerable object.
    [<CompiledName("OfSeq")>]
    let ofSeq seq =
        (empty, seq)
        ||> Seq.fold (fun tree el ->
            add el tree)

    /// Returns a sequence of tuples <c>(lower, upper)</c>
    /// containing the intervals of values in the set.
    [<CompiledName("Intervals")>]
    let rec intervals tree =
        seq {
        match tree with
        | Empty -> ()
        | Node (lowerBound, upperBound, left, right) ->
            // Produce the sequence for the left subtree.
            yield! intervals left

            // Return the current interval.
            yield lowerBound, upperBound

            // Produce the sequence for the right subtree.
            yield! intervals right }

    /// Returns the highest (greatest) value in the set.
    [<CompiledName("MaxElement")>]
    let rec maxElement tree =
        match tree with
        | Empty ->
            invalidArg "tree" "Cannot retrieve the maximum element of an empty set."
        | Node (_,_,_,(Node (_,_,_,_) as right)) ->
            maxElement right
        | Node (_,maxEl,_,_) ->
            maxEl

    /// Returns the lowest (least) value in the set. 
    [<CompiledName("MinElement")>]
    let rec minElement tree =
        match tree with
        | Empty ->
            invalidArg "tree" "Cannot retrieve the minimum element of an empty set."
        | Node (_,_,(Node (_,_,_,_) as left),_) ->
            minElement left
        | Node (minEl,_,_,_) ->
            minEl

    /// Splits the set into two sets containing the elements for which
    /// the given predicate returns true and false respectively.
    [<CompiledName("Partition")>]
    let partition predicate set =
        ((empty, empty), set)
        ||> fold (fun (trueSet, falseSet) el ->
            if predicate el then
                add el trueSet,
                falseSet
            else
                trueSet,
                add el falseSet)

    /// Returns a new set with the elements of the second set removed from the first.
    [<CompiledName("Difference")>]
    let difference set1 set2 =
        // OPTIMIZE : This could probably be re-implemented to walk both
        // trees at once, building a new set from the bottom up. This would
        // avoid multiple traversals of both set trees and the result set tree.

        // TEMP : This works, but it's **slow**.
        (empty, set1)
        ||> fold (fun set1' el ->
            if contains el set2 then
                set1'
            else
                add el set1')

    /// Computes the intersection of the two sets.
    [<CompiledName("Intersect")>]
    let intersect set1 set2 =
        // OPTIMIZE : This could probably be re-implemented to walk both
        // trees at once, building a new set from the bottom up. This would
        // avoid multiple traversals of both set trees and the result set tree.

        // TEMP : This works, but it's **slow**.
        let smaller, larger =
            if count set1 < count set2 then
                set1, set2
            else set2, set1

        (empty, smaller)
        ||> fold (fun intersection el ->
            if contains el larger then
                add el intersection
            else
                intersection)    

    /// Computes the union of the two sets.
    [<CompiledName("Union")>]
    let union set1 set2 =
        // OPTIMIZE : This could probably be re-implemented to walk both
        // trees at once, building a new set from the bottom up. This would
        // avoid multiple traversals of both set trees and the result set tree.

        // TEMP : This works, but it's **slow**.
        let smaller, larger =
            if count set1 < count set2 then
                set1, set2
            else set2, set1

        (larger, smaller)
        ||> fold (fun union el ->
            add el union)


