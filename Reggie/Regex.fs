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

namespace Reggie

open System.Diagnostics
open ExtCore.Control
open ExtCore.Control.Cps
open Reggie.SpecializedCollections

(*  Turn off warning about uppercase variable identifiers; some variables
    in the code below are are named using the F# backtick syntax so they
    can use names which closely match those in the paper. *)
#nowarn "49"


/// <summary>An extended regular expression.</summary>
/// <remarks>
/// <para>
/// This type represents a regular expression "extended" with intersection
/// and complement operations. These operations are still closed so the language
/// defined by an instance of this type is still considered a regular language.
/// </para>
/// <para>
/// The ordering of the cases in this type is important because it is used by the
/// F# compiler when it generates the comparison implementation for this type.
/// The comparison function is a critical part of the rewriting / simplification /
/// normalization logic, so re-ordering the cases of this type can significantly
/// change the behavior of the rest of the program.
/// </para>
/// </remarks>
[<DebuggerDisplay("{DebuggerDisplay,nq}")>]
type Regex =
    /// The empty string.
    | Epsilon
    /// A set of characters.
    | CharacterSet of CharSet

    /// Negation (language complement).
    | Negate of Regex
    /// Kleene *-closure.
    /// The specified Regex will be matched zero (0) or more times.
    | Star of Regex

    /// Concatenation. A Regex immediately followed by another Regex.
    | Concat of Regex * Regex
    /// Choice between two regular expressions (i.e., boolean OR).
    | Or of Regex * Regex
    /// Intersection of two regular expressions (i.e., boolean AND).
    | And of Regex * Regex

    /// Infrastructure. Only for use with DebuggerDisplayAttribute.
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private this.DebuggerDisplay
        with get () =
            match this with
            | Epsilon ->
                "\u03f5"
            | CharacterSet charSet ->
                charSet.ToString ()
            | Negate regex ->
                sprintf "\u00ac(%s)" regex.DebuggerDisplay
            | Star regex ->
                sprintf "(%s)*" regex.DebuggerDisplay
            | Concat (r, s) ->
                r.DebuggerDisplay + s.DebuggerDisplay
            | Or (r, s) ->
                sprintf "(%s|%s)" r.DebuggerDisplay s.DebuggerDisplay
            | And (r, s) ->
                sprintf "(%s&%s)" r.DebuggerDisplay s.DebuggerDisplay

    /// Determines if a specified Regex is 'nullable',
    /// i.e., it accepts the empty string (epsilon).
    static member private IsNullableImpl regex =
        cont {
        match regex with
        | Epsilon
        | Star _ ->
            return true
        | CharacterSet _
        | Negate (CharacterSet _) ->
            return false
        | Negate regex ->
            let! result = Regex.IsNullableImpl regex
            return not result
        | Concat (a, b)
        | And (a, b) ->
            // IsNullable(a) && IsNullable(b)
            let! aNullable = Regex.IsNullableImpl a
            if aNullable then
                return! Regex.IsNullableImpl b
            else
                return false
        | Or (a, b) ->
            // IsNullable(a) || IsNullable(b)
            let! aNullable = Regex.IsNullableImpl a
            if aNullable then
                return true
            else
                return! Regex.IsNullableImpl b
        }

    /// Determines if a specified Regex is 'nullable',
    /// i.e., it accepts the empty string (epsilon).
    static member IsNullable (regex : Regex) =
        // OPTIMIZATION : Immediately return the result for some patterns instead of calling
        // the continuation-based method -- this eliminates the overhead of creating/calling
        // the continuations for some very common cases.
        match regex with
        | Epsilon
        | Star _ ->
            true
        | CharacterSet _
        | Negate (CharacterSet _) ->
            false
        | _ ->
            Regex.IsNullableImpl regex id

    //
    static member private PrintFSharpCodeImpl regex (indentedWriter : System.CodeDom.Compiler.IndentedTextWriter) =
        cont {
        // TODO : Use the indented writer to pretty-print the code so it's more readable.

        match regex with
        | Epsilon ->
            indentedWriter.Write "Epsilon"
        | CharacterSet charSet ->
            indentedWriter.Write "CharacterSet "

            // Is the charset empty?
            if CharSet.isEmpty charSet then
                indentedWriter.Write "CharSet.Empty"
            else
                indentedWriter.Write "(CharSet.OfIntervals [| "

                // Write out the intervals in the charset as tuples.
                CharSet.IterIntervals ((fun lo hi ->
                    Printf.fprintf indentedWriter "'\\u%04x', '\\u%04x'; " (int lo) (int hi)),
                    charSet)

                // Close the array, then close the parentheses for the CharacterSet.
                indentedWriter.Write "|])"

        | Negate regex ->
            // Open the pattern.
            indentedWriter.Write "Negate ("

            // Write the nested pattern.
            do! Regex.PrintFSharpCodeImpl regex indentedWriter

            // Close the pattern.
            indentedWriter.Write ")"
        | Star regex ->
            // Open the pattern.
            indentedWriter.Write "Star ("

            // Write the nested pattern.
            do! Regex.PrintFSharpCodeImpl regex indentedWriter

            // Close the pattern.
            indentedWriter.Write ")"

        | Concat (r, s) ->
            // Open the pattern.
            indentedWriter.Write "Concat ("

            // Write the first nested pattern.
            do! Regex.PrintFSharpCodeImpl r indentedWriter

            // Write a comma to separate the first and second patterns.
            indentedWriter.Write ", "

            // Write the second nested pattern.
            do! Regex.PrintFSharpCodeImpl s indentedWriter

            // Close the pattern.
            indentedWriter.Write ")"

        | Or (r, s) ->
            // Open the pattern.
            indentedWriter.Write "Or ("

            // Write the first nested pattern.
            do! Regex.PrintFSharpCodeImpl r indentedWriter

            // Write a comma to separate the first and second patterns.
            indentedWriter.Write ", "

            // Write the second nested pattern.
            do! Regex.PrintFSharpCodeImpl s indentedWriter

            // Close the pattern.
            indentedWriter.Write ")"

        | And (r, s) ->
            // Open the pattern.
            indentedWriter.Write "And ("

            // Write the first nested pattern.
            do! Regex.PrintFSharpCodeImpl r indentedWriter

            // Write a comma to separate the first and second patterns.
            indentedWriter.Write ", "

            // Write the second nested pattern.
            do! Regex.PrintFSharpCodeImpl s indentedWriter

            // Close the pattern.
            indentedWriter.Write ")"
        }

    //
    static member PrintFSharpCode (regex, textWriter : System.IO.TextWriter) =
        checkNonNull "regex" regex
        checkNonNull "textWriter" textWriter

        // Wrap the specified TextWriter instance with IndentedTextWriter so it's easier
        // for the recursive implementation to work with.
        use indentedTextWriter = new System.CodeDom.Compiler.IndentedTextWriter (textWriter, "    ")

        // Print the code to re-create the Regex into the TextWriter.
        Regex.PrintFSharpCodeImpl regex indentedTextWriter id

    //
    static member PrintFSharpCode regex =
        // Initialize the StringBuilder to a reasonable size to avoid repeated small resizes.
        let sb = System.Text.StringBuilder (1000)

        // Create a StringWriter wrapping the StringBuilder;
        // print the code to re-create the Regex into the StringWriter.
        use stringWriter = new System.IO.StringWriter(sb)
        Regex.PrintFSharpCode (regex, stringWriter)

        // Return the code string.
        sb.ToString ()

#if DEBUG
    // TEMP : For testing only, remove this later to restore the default ToString() implementation.
    override this.ToString () =
        Regex.PrintFSharpCode this
#endif

    // TODO : Implement a method for checking equivalence of two regular expressions?
    //        This is possible for regular expressions, but is it possible for extended regular expressions?


/// Active patterns which simplify matching of special <see cref="Regex"/> instances.
[<AutoOpen>]
module RegexPatterns =
    /// Partial active pattern which may be used to detect the 'empty' or 'null' language.
    let inline (|Empty|_|) regex =
        match regex with
        | CharacterSet charSet
            when CharSet.isEmpty charSet ->
            Some ()
        | _ ->
            None

    /// Partial active pattern which may be used to detect a pattern which matches one (1) instance of any character.
    let inline (|Any|_|) regex =
        match regex with
        | Negate Empty ->
            Some ()
        | _ ->
            None


/// 'Smart' constructors for Regex.
/// These should *always* be used to create new Regex instances because they ensure the
/// resulting Regex is in a normal form; this is very important for minimizing the number
/// of states in the DFA constructed from the Regex.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Regex =
    /// The 'epsilon' pattern, which matches (accepts) an empty string.
    [<CompiledName("Epsilon")>]
    let epsilon : Regex =
        Epsilon

    /// The regular expression which never matches (accepts) anything.
    [<CompiledName("Empty")>]
    let empty : Regex =
        CharacterSet CharSet.empty

    /// The regular expression which matches exactly one (1) instance of any character.
    [<CompiledName("Any")>]
    let any : Regex =
        Negate empty

    /// Is the regular expression empty?
    [<CompiledName("IsEmpty")>]
    let isEmpty regex =
        match regex with
        | Empty ->
            true
        | _ ->
            false

    /// Returns a new regular expression which matches exactly one (1) instance of the specified character.
    [<CompiledName("OfCharacter")>]
    let inline ofChar c =
        CharacterSet <| CharSet.singleton c

    /// Returns a new regular expression which matches exactly one (1) instance
    /// of any character in the specified set.
    [<CompiledName("OfCharSet")>]
    let inline ofCharSet (set : CharSet) : Regex =
        CharacterSet set

    /// TraceSource which can be enabled to trace Regex simplification steps.
    let private regexSimplifyTrace = TraceSource ("Reggie.Regex.Simplify")

    /// <summary>
    /// Simplify and normalize a regular expression, one step at a time.
    /// </summary>
    /// <remarks>
    /// <para>
    /// This function is similar to 'simplifyRec' but only performs zero or one
    /// simplification or normalization step each time it's called; 'simplifyRec'
    /// recursively processes the regex until it reaches a fixpoint, which improves
    /// performance by avoiding the creation of unnecessary tree nodes.
    /// </para>
    /// <para>
    /// 'simplifyStep' is used for analysis and debugging, since it allows the
    /// fixpoint-finding loop to be moved outside of the function itself; for example,
    /// it is used by 'simplifySteps' to produce a sequence of regexes showing how
    /// a particular regex is simplified/normalized by the rewrite rules.
    /// </para>
    /// <para>
    /// NOTE: It is extremely important to the correctness of this function to avoid *any*
    /// recursive simplification calls via the F# 'return!' keyword.
    /// </para>
    /// </remarks>
    let rec internal simplifyStep regex =
#if DEBUG && TRACE
        // For testing purposes, it's sometimes useful to print out the simplification steps.
        // Don't call Regex.PrintFSharpCode unless the output is actually going to be used,
        // as it's relatively expensive in terms of performance.
        if regexSimplifyTrace.Switch.ShouldTrace TraceEventType.Verbose then
            regexSimplifyTrace.TraceInformation (Regex.PrintFSharpCode regex)
#endif

        cont {
        match regex with
        | Epsilon
        | Any
        | CharacterSet _ ->
            // Return None, because no simplification was performed for the regex.
            return None

        (* Negate *)
        // Double-negation cancels out.
        | Negate (Negate regex) ->
            return Some regex
        | Negate negatedRegex ->
            // Simplify the inner regex first.
            let! simpNegatedRegex = simplifyStep negatedRegex
            match simpNegatedRegex with
            | Some negatedRegex ->
                // Return a new Negate node with the simplified inner regex.
                return Some <| Negate negatedRegex
            | None ->
                // Regex wasn't simplified.
                match negatedRegex with
                | Epsilon ->
                    return Some empty

                // Use DeMorgan's rules to simplify negation of Or and And patterns when possible.
                // This isn't specified in the original paper, but it helps to compact the regex.
                | Or (regex1, regex2) ->
                    return Some <| And (Negate regex1, Negate regex2)
                | And (regex1, regex2) ->
                    return Some <| Or (Negate regex1, Negate regex2)

                // Double-negation cancels out.
                | Negate regex ->
                    // 'regex' is already simplified, so it can be returned without simplifying again.
                    return Some regex

                | _ ->
                    // No other simplifications to make.
                    return None

        (* Star *)
        // The Star operation is idempotent -- nested Stars are equivalent to a single Star.
        | Star (Star regex) ->
            return Some <| Star regex

        // Can't simplify this case further, so don't bother trying.
        | Star (CharacterSet c) when not (CharSet.isEmpty c) ->
            return None

        | Star starredRegex ->
            // Try to simplify the inner regex first.
            let! simpRegex = simplifyStep starredRegex
            match simpRegex with
            | Some starredRegex ->
                // Return a new Star node with the simplified inner regex.
                return Some <| Star starredRegex
            | None ->
                // Couldn't simplify the inner regex further, so now try to simplify this Star node.
                match starredRegex with
                | Epsilon
                | Empty ->
                    return Some Epsilon

                // The Star operation is idempotent -- nested Stars are equivalent to a single Star.
                | Star _ ->
                    // 'starredRegex' is already simplified, so it can be returned without simplifying again.
                    return Some starredRegex

                | _ ->
                    return None

        (* Concat *)
        // Nested Concat patterns should skew towards the right.
        | Concat (Concat (r, s), t) ->
            return Some <| Concat (r, Concat (s, t))

        // These cases occur quite frequently so we match them here to improve performance
        // (by avoiding attempting to simplify further, which allocates continuations and
        // additional CharacterSet objects).
        | Concat ((Empty as r), _)
        | Concat (_, (Empty as r)) ->
            return Some r
        | Concat (CharacterSet _, CharacterSet _) ->
            // Can't simplify this case.
            return None

        | Concat (regex1, regex2) ->
            // Try to simplify the first sub-regex.
            let! simpRegex1 = simplifyStep regex1
            match simpRegex1 with
            | Some regex1 ->
                // Return a new Concat node with the simplified regex.
                return Some <| Concat (regex1, regex2)
            | None ->
                // Try to simplify the second sub-regex.
                let! simpRegex2 = simplifyStep regex2
                match simpRegex2 with
                | Some regex2 ->
                    // Return a new Concat node with the simplified regex.
                    return Some <| Concat (regex1, regex2)
                | None ->
                    // Neither of the sub-regexes could be simplified, so try to simplify this node.
                    match regex1, regex2 with
                    | regex, Epsilon
                    | Epsilon, regex ->
                        return Some regex
                    | Empty, _
                    | _, Empty ->
                        return Some empty

                    // Nested Concat patterns should skew towards the right.
                    | Concat (r, s), t ->
                        return Some <| Concat (r, Concat (s, t))

                    | Star s, Star t
                        // The equivalence here is only an approximation.
                        // If we wanted to, we could implement and use a more powerful test for regular expression equivalence.
                        when s == t || s = t ->
                        // 'regex1' is already simplified, so return it.
                        return Some regex1

                    // TODO : Implement rewrite rules to distribute Concat over Or (and perhaps And)?

                    | _, _ ->
                        // Base case: Concat (regex1, regex2) can't be simplified any further.
                        return None

        (* And *)

        // The next two rules ensure that nested And patterns are skewed to the right.
        // The And operation is associative; to enforce confluence of the rewrite system,
        // the sub-patterns are also sorted when creating the right-skewed tree.
        // E.g., And (r, And (s, t)) is rewritten to And (And (a, b), c) where a <= b <= c.
        | And (And (x, y), And (z, w)) ->
            let mutable a = x
            let mutable b = y
            let mutable c = z
            let mutable d = w
            TupleUtils.sortFour (&a, &b, &c, &d)
            return Some <| And (a, And (b, And (c, d)))

        | And (And (r, s), t) ->
            let mutable a = r
            let mutable b = s
            let mutable c = t
            TupleUtils.sortThree (&a, &b, &c)
            return Some <| And (a, And (b, c))

        | And (regex1, regex2) ->
            // Try to simplify the first sub-regex.
            let! simpRegex1 = simplifyStep regex1
            match simpRegex1 with
            | Some regex1 ->
                // Return a new And node with the simplified regex.
                return Some <| And (regex1, regex2)
            | None ->
                // Try to simplify the second sub-regex.
                let! simpRegex2 = simplifyStep regex2
                match simpRegex2 with
                | Some regex2 ->
                    // Return a new And node with the simplified regex.
                    return Some <| And (regex1, regex2)
                | None ->
                    // Neither of the sub-regexes could be simplified, so try to simplify this node.
                    match regex1, regex2 with
                    | Empty, _
                    | _, Empty ->
                        return Some empty

                    | Any, regex
                    | regex, Any ->
                        return Some regex

                    | Epsilon, Epsilon ->
                        return Some Epsilon

                    // Any language AND-ed with Epsilon (other than another Epsilon) produces the null (empty) language.
                    // This works because we've already recursively simplified both regexes here first, and we've already
                    // handled the And (Epsilon, Epsilon) case.
                    | Epsilon, _
                    | _, Epsilon ->
                        return Some empty

                    // The next two rules ensure that nested And patterns are skewed to the right.
                    // The And operation is associative; to enforce confluence of the rewrite system,
                    // the sub-patterns are also sorted when creating the right-skewed tree.
                    // E.g., And (r, And (s, t)) is rewritten to And (And (a, b), c) where a <= b <= c.
                    | And (x, y), And (z, w) ->
                        let mutable a = x
                        let mutable b = y
                        let mutable c = z
                        let mutable d = w
                        TupleUtils.sortFour (&a, &b, &c, &d)
                        return Some <| And (a, And (b, And (c, d)))

                    | And (r, s), t ->
                        let mutable a = r
                        let mutable b = s
                        let mutable c = t
                        TupleUtils.sortThree (&a, &b, &c)
                        return Some <| And (a, And (b, c))

                    (* Rewrite rules which are extremely important since they compact the regex, thereby reducing the number of DFA states. *)
                    | CharacterSet s1, CharacterSet s2 ->
                        return
                            CharSet.intersect s1 s2
                            |> CharacterSet
                            |> Some

                    // Simplify via DeMorgan's laws.
                    | Negate (CharacterSet charSet1), Negate (CharacterSet charSet2) ->
                        return
                            CharSet.union charSet1 charSet2
                            |> CharacterSet
                            |> Negate
                            |> Some

                    | CharacterSet positiveSet, Negate (CharacterSet negativeSet)
                    | Negate (CharacterSet negativeSet), CharacterSet positiveSet ->
                        return
                            CharSet.difference positiveSet negativeSet
                            |> CharacterSet
                            |> Some

                    // NOTE : These next two rewrite rules aren't specified in the original paper,
                    //        but are useful for keeping the regex compact in certain cases.
                    | Star (CharacterSet charSet1), Star (CharacterSet charSet2) ->
                        // No simplification needed for Star (CharacterSet _), so just return it.
                        return
                            CharSet.intersect charSet1 charSet2
                            |> CharacterSet
                            |> Star
                            |> Some

                    | _, _ ->
                        // Check whether this node is and-ing a regex with itself.
                        if regex1 == regex2 || regex1 = regex2 then
                            return Some regex1
                        else
                            // Compare/sort the two regexes. This simplifies the compilation code and
                            // also -- crucially -- speeds it up since it allows the compiler-generated structural
                            // equality code to be used as an (approximate) equivalence test.
                            if regex2 < regex1 then
                                return Some <| And (regex2, regex1)
                            else
                                // Base case: And (regex1, regex2) can't be simplified any further.
                                return None

        (* Or *)

        // The next two rules ensure that nested Or patterns are skewed to the right.
        // The Or operation is associative; to enforce confluence of the rewrite system,
        // the sub-patterns are also sorted when creating the right-skewed tree.
        // E.g., Or (Or (r, s), t) is rewritten to Or (Or a, Or (b, c)) where a <= b <= c.
        | Or (Or (x, y), Or (z, w)) ->
            let mutable a = x
            let mutable b = y
            let mutable c = z
            let mutable d = w
            TupleUtils.sortFour (&a, &b, &c, &d)
            return Some <| Or (a, Or (b, Or (c, d)))

        | Or (Or (r, s), t) ->
            let mutable a = r
            let mutable b = s
            let mutable c = t
            TupleUtils.sortThree (&a, &b, &c)
            return Some <| Or (a, Or (b, c))

        // This case occurs quite frequently so we match it here to improve performance
        // (by avoiding attempting to simplify further, which allocates continuations and
        // additional CharacterSet objects).
        | Or ((Empty as r), Empty) ->
            return Some r

        | Or (regex1, regex2) ->
            // Try to simplify the first sub-regex.
            let! simpRegex1 = simplifyStep regex1
            match simpRegex1 with
            | Some regex1 ->
                // Return a new Or node with the simplified regex.
                return Some <| Or (regex1, regex2)
            | None ->
                // Try to simplify the second sub-regex.
                let! simpRegex2 = simplifyStep regex2
                match simpRegex2 with
                | Some regex2 ->
                    // Return a new Or node with the simplified regex.
                    return Some <| Or (regex1, regex2)
                | None ->
                    // Neither of the sub-regexes could be simplified, so try to simplify this node.

                    // TODO: Sort the two regexes before matching on them; this will simplify
                    //       some of the rewriting logic below since we won't need to check both ways
                    //       for certain patterns.

                    match regex1, regex2 with
                    | Epsilon, Epsilon ->
                        return Some Epsilon

                    // Handle nested Or patterns with Epsilon as one of the inputs (in each pattern).
                    // Epsilon only needs to appear once in each such chain of Or patterns.
                    | Epsilon, (Or (Epsilon, _) as r)
                    | (Or (Epsilon, _) as r), Epsilon ->
                        return Some r

                    // The next two rules ensure that nested Or patterns are skewed to the right.
                    // The Or operation is associative; to enforce confluence of the rewrite system,
                    // the sub-patterns are also sorted when creating the right-skewed tree.
                    // E.g., Or (Or (r, s), t) is rewritten to Or (Or a, Or (b, c)) where a <= b <= c.
                    | Or (x, y), Or (z, w) ->
                        let mutable a = x
                        let mutable b = y
                        let mutable c = z
                        let mutable d = w
                        TupleUtils.sortFour (&a, &b, &c, &d)
                        return Some <| Or (a, Or (b, Or (c, d)))

                    | Or (r, s), t ->
                        let mutable a = r
                        let mutable b = s
                        let mutable c = t
                        TupleUtils.sortThree (&a, &b, &c)
                        return Some <| Or (a, Or (b, c))

                    (* Rewrite rules for 'Any' and 'Empty' *)

                    | Empty, regex
                    | regex, Empty ->
                        // 'regex' is already simplified, so we can just return it.
                        return Some regex

                    | Any, _
                    | _, Any ->
                        return Some any

                    (* Rewrite rules which are extremely important since they compact the regex, thereby reducing the number of DFA states. *)

                    | CharacterSet charSet1, CharacterSet charSet2 ->
                        return
                            CharSet.union charSet1 charSet2
                            |> CharacterSet
                            |> Some

                    // Simplify via DeMorgan's laws.
                    | Negate (CharacterSet charSet1), Negate (CharacterSet charSet2) ->
                        return
                            CharSet.intersect charSet1 charSet2
                            |> CharacterSet
                            |> Negate
                            |> Some

        //            | CharacterSet positiveSet, Negate (CharacterSet negativeSet)
        //            | Negate (CharacterSet negativeSet), CharacterSet positiveSet ->
        //                return! notImpl ""

                    // NOTE : This rewrite rule isn't specified in the original paper,
                    //        but is important for keeping the regex compact in certain cases.
                    | Star (CharacterSet charSet1), Star (CharacterSet charSet2) ->
                        // No simplification needed for Star (CharacterSet _), so just return it.
                        return
                            CharSet.union charSet1 charSet2
                            |> CharacterSet
                            |> Star
                            |> Some

                    | _, _ ->
                        // Check whether this node is or-ing a regex with itself.
                        if regex1 == regex2 || regex1 = regex2 then
                            return Some regex1
                        else
                            // Compare/sort the two regexes. This simplifies the compilation code and
                            // also -- crucially -- speeds it up since it allows the compiler-generated structural
                            // equality code to be used as an (approximate) equivalence test.
                            if regex2 < regex1 then
                                return Some <| Or (regex2, regex1)
                            else
                                // Base case: Or (regex1, regex2) can't be simplified any further, so return it.
                                return None
        }

    /// Recursively simplify and normalize a regular expression.
    let rec internal simplifyRec regex =
#if DEBUG && TRACE
        // For testing purposes, it's sometimes useful to print out the simplification steps.
        // Don't call Regex.PrintFSharpCode unless the output is actually going to be used,
        // as it's relatively expensive in terms of performance.
        if regexSimplifyTrace.Switch.ShouldTrace TraceEventType.Verbose then
            regexSimplifyTrace.TraceInformation (Regex.PrintFSharpCode regex)
#endif

        cont {
        match regex with
        | Epsilon
        | Any
        | CharacterSet _ ->
            return regex

        (* Negate *)
        // Double-negation cancels out.
        | Negate (Negate regex) ->
            return! simplifyRec regex
        | Negate regex' ->
            // Simplify the inner regex first.
            let! regex' = simplifyRec regex'
            match regex' with
            | Epsilon ->
                return empty

            // Use DeMorgan's rules to simplify negation of Or and And patterns when possible.
            // This isn't specified in the original paper, but it helps to compact the regex.
            | Or (regex1, regex2) ->
                return! simplifyRec <| And (Negate regex1, Negate regex2)
            | And (regex1, regex2) ->
                return! simplifyRec <| Or (Negate regex1, Negate regex2)

            // Double-negation cancels out.
            | Negate regex ->
                // 'regex' is already simplified, so it can be returned without simplifying again.
                return regex

            | _ ->
                // Determine if we were able to simplify the inner regex.
                // If not, return the original input regex instead of creating a new one
                // to cut down on allocations and improve performance.
                if regex == regex' || regex = regex' then
                    return regex
                else
                    return Negate regex'

        (* Star *)
        // The Star operation is idempotent -- nested Stars are equivalent to a single Star.
        | Star (Star regex) ->
            return! simplifyRec <| Star regex

        // Can't simplify this case further, so don't bother trying.
        | Star (CharacterSet c) when not (CharSet.isEmpty c) ->
            return regex

        | Star regex ->
            // Simplify the inner regex first.
            let! regex = simplifyRec regex
            match regex with
            | Epsilon
            | Empty ->
                return Epsilon

            // The Star operation is idempotent -- nested Stars are equivalent to a single Star.
            | Star _ ->
                // 'regex' is already simplified, so it can be returned without simplifying again.
                return regex

            | _ ->
                return Star regex

        (* Concat *)
        // Nested Concat patterns should skew towards the right.
        | Concat (Concat (r, s), t) ->
            return! simplifyRec <| Concat (r, Concat (s, t))

        // These cases occur quite frequently so we match them here to improve performance
        // (by avoiding attempting to simplify further, which allocates continuations and
        // additional CharacterSet objects).
        | Concat ((Empty as r), _)
        | Concat (_, (Empty as r)) ->
            return r
        | Concat (CharacterSet _, CharacterSet _) ->
            return regex

        | Concat (regex1, regex2) ->
            // Simplify the two sub-regexes first.
            let! regex1 = simplifyRec regex1
            let! regex2 = simplifyRec regex2

            match regex1, regex2 with
            | regex, Epsilon
            | Epsilon, regex ->
                // 'regex' is already simplified, so we can just return it.
                return regex
            | Empty, _
            | _, Empty ->
                return empty

            // Nested Concat patterns should skew towards the right.
            | Concat (r, s), t ->
                return! simplifyRec <| Concat (r, Concat (s, t))

            | Star s, Star t
                // The equivalence here is only an approximation.
                // If we wanted to, we could implement and use a more powerful test for regular expression equivalence.
                when s == t || s = t ->
                // 'regex1' is already simplified, so just return it.
                return regex1

            // TODO : Implement rewrite rules to distribute Concat over Or (and perhaps And)?

            | _, _ ->
                // Base case: Concat (regex1, regex2) can't be simplified any further, so return it.
                return Concat (regex1, regex2)

        (* And *)

        // The next two rules ensure that nested And patterns are skewed to the right.
        // The And operation is associative; to enforce confluence of the rewrite system,
        // the sub-patterns are also sorted when creating the right-skewed tree.
        // E.g., And (r, And (s, t)) is rewritten to And (And (a, b), c) where a <= b <= c.
        | And (And (x, y), And (z, w)) ->
            let mutable a = x
            let mutable b = y
            let mutable c = z
            let mutable d = w
            TupleUtils.sortFour (&a, &b, &c, &d)
            return! simplifyRec <| And (a, And (b, And (c, d)))

        | And (And (r, s), t) ->
            let mutable a = r
            let mutable b = s
            let mutable c = t
            TupleUtils.sortThree (&a, &b, &c)
            return! simplifyRec <| And (a, And (b, c))

        | And (regex1, regex2) ->
            // Simplify the two sub-regexes first.
            let! regex1 = simplifyRec regex1
            let! regex2 = simplifyRec regex2

            match regex1, regex2 with
            | Empty, _
            | _, Empty ->
                return empty

            | Any, regex
            | regex, Any ->
                return regex

            | Epsilon, Epsilon ->
                return Epsilon

            // Any language AND-ed with Epsilon (other than another Epsilon) produces the null (empty) language.
            // This works because we've already recursively simplified both regexes here first, and we've already
            // handled the And (Epsilon, Epsilon) case.
            | Epsilon, _
            | _, Epsilon ->
                return empty

            // The next two rules ensure that nested And patterns are skewed to the right.
            // The And operation is associative; to enforce confluence of the rewrite system,
            // the sub-patterns are also sorted when creating the right-skewed tree.
            // E.g., And (r, And (s, t)) is rewritten to And (And (a, b), c) where a <= b <= c.
            | And (x, y), And (z, w) ->
                let mutable a = x
                let mutable b = y
                let mutable c = z
                let mutable d = w
                TupleUtils.sortFour (&a, &b, &c, &d)
                return! simplifyRec <| And (a, And (b, And (c, d)))

            | And (r, s), t ->
                let mutable a = r
                let mutable b = s
                let mutable c = t
                TupleUtils.sortThree (&a, &b, &c)
                return! simplifyRec <| And (a, And (b, c))

            (* Rewrite rules which are extremely important since they compact the regex, thereby reducing the number of DFA states. *)
            | CharacterSet s1, CharacterSet s2 ->
                return
                    CharSet.intersect s1 s2
                    |> CharacterSet

            // Simplify via DeMorgan's laws.
            | Negate (CharacterSet charSet1), Negate (CharacterSet charSet2) ->
                return
                    CharSet.union charSet1 charSet2
                    |> CharacterSet
                    |> Negate

            | CharacterSet positiveSet, Negate (CharacterSet negativeSet)
            | Negate (CharacterSet negativeSet), CharacterSet positiveSet ->
                return
                    CharSet.difference positiveSet negativeSet
                    |> CharacterSet

            // NOTE : These next two rewrite rules aren't specified in the original paper,
            //        but are useful for keeping the regex compact in certain cases.
            | Star (CharacterSet charSet1), Star (CharacterSet charSet2) ->
                // No simplification needed for Star (CharacterSet _), so just return it.
                return!
                    CharSet.intersect charSet1 charSet2
                    |> CharacterSet
                    |> Star
                    |> simplifyRec

            | _, _ ->
                // Base case: And (regex1, regex2) can't be simplified any further.
                if regex1 == regex2 || regex1 = regex2 then
                    return regex1
                else
                    // Compare/sort the two regexes. This simplifies the compilation code and
                    // also -- crucially -- speeds it up since it allows the compiler-generated structural
                    // equality code to be used as an (approximate) equivalence test.
                    if regex2 < regex1 then
                        return And (regex2, regex1)
                    else
                        return And (regex1, regex2)

        (* Or *)

        // The next two rules ensure that nested Or patterns are skewed to the right.
        // The Or operation is associative; to enforce confluence of the rewrite system,
        // the sub-patterns are also sorted when creating the right-skewed tree.
        // E.g., Or (Or (r, s), t) is rewritten to Or (Or a, Or (b, c)) where a <= b <= c.
        | Or (Or (x, y), Or (z, w)) ->
            let mutable a = x
            let mutable b = y
            let mutable c = z
            let mutable d = w
            TupleUtils.sortFour (&a, &b, &c, &d)
            return! simplifyRec <| Or (a, Or (b, Or (c, d)))

        | Or (Or (r, s), t) ->
            let mutable a = r
            let mutable b = s
            let mutable c = t
            TupleUtils.sortThree (&a, &b, &c)
            return! simplifyRec <| Or (a, Or (b, c))

        // This case occurs quite frequently so we match it here to improve performance
        // (by avoiding attempting to simplify further, which allocates continuations and
        // additional CharacterSet objects).
        | Or ((Empty as r), Empty) ->
            return r

        | Or (regex1, regex2) ->
            // Simplify the two sub-regexes first.
            let! regex1 = simplifyRec regex1
            let! regex2 = simplifyRec regex2

            // TODO: Sort the two regexes before matching on them; this will simplify
            //       some of the rewriting logic below since we won't need to check both ways
            //       for certain patterns.

            match regex1, regex2 with
            | Epsilon, Epsilon ->
                return Epsilon

            // Handle nested Or patterns with Epsilon as one of the inputs (in each pattern).
            // Epsilon only needs to appear once in each such chain of Or patterns.
            | Epsilon, (Or (Epsilon, _) as r)
            | (Or (Epsilon, _) as r), Epsilon ->
                return r

            // The next two rules ensure that nested Or patterns are skewed to the right.
            // The Or operation is associative; to enforce confluence of the rewrite system,
            // the sub-patterns are also sorted when creating the right-skewed tree.
            // E.g., Or (Or (r, s), t) is rewritten to Or (Or a, Or (b, c)) where a <= b <= c.
            | Or (x, y), Or (z, w) ->
                let mutable a = x
                let mutable b = y
                let mutable c = z
                let mutable d = w
                TupleUtils.sortFour (&a, &b, &c, &d)
                return! simplifyRec <| Or (a, Or (b, Or (c, d)))

            | Or (r, s), t ->
                let mutable a = r
                let mutable b = s
                let mutable c = t
                TupleUtils.sortThree (&a, &b, &c)
                return! simplifyRec <| Or (a, Or (b, c))

            (* Rewrite rules for 'Any' and 'Empty' *)

            | Empty, regex
            | regex, Empty ->
                // 'regex' is already simplified, so we can just return it.
                return regex

            | Any, _
            | _, Any ->
                return any

            (* Rewrite rules which are extremely important since they compact the regex, thereby reducing the number of DFA states. *)

            | CharacterSet charSet1, CharacterSet charSet2 ->
                return
                    CharSet.union charSet1 charSet2
                    |> CharacterSet

            // Simplify via DeMorgan's laws.
            | Negate (CharacterSet charSet1), Negate (CharacterSet charSet2) ->
                return
                    CharSet.intersect charSet1 charSet2
                    |> CharacterSet
                    |> Negate

//            | CharacterSet positiveSet, Negate (CharacterSet negativeSet)
//            | Negate (CharacterSet negativeSet), CharacterSet positiveSet ->
//                return! notImpl ""

            // NOTE : This rewrite rule isn't specified in the original paper,
            //        but is important for keeping the regex compact in certain cases.
            | Star (CharacterSet charSet1), Star (CharacterSet charSet2) ->
                // No simplification needed for Star (CharacterSet _), so just return it.
                return
                    CharSet.union charSet1 charSet2
                    |> CharacterSet
                    |> Star

            | _, _ ->
                // Base case: Or (regex1, regex2) can't be simplified any further, so return it.
                if regex1 == regex2 || regex1 = regex2 then
                    return regex1
                else
                    // Compare/sort the two regexes. This simplifies the compilation code and
                    // also -- crucially -- speeds it up since it allows the compiler-generated structural
                    // equality code to be used as an (approximate) equivalence test.
                    if regex2 < regex1 then
                        return Or (regex2, regex1)
                    else
                        return Or (regex1, regex2)
        }

    /// Returns a new regular expression which matches the given
    /// regular expression zero or more times.
    [<CompiledName("CreateStar")>]
    let star (regex : Regex) : Regex =
        // Create the Star pattern, then simplify it before returning.
        simplifyRec (Star regex) id

    /// Creates a normalized Regex.Negate from the specified Regex.
    [<CompiledName("CreateNegate")>]
    let negate (regex : Regex) : Regex =
        // Create the Negate pattern, then simplify it before returning.
        simplifyRec (Negate regex) id

    /// Concatenates two regular expressions so they'll be matched sequentially.
    [<CompiledName("CreateConcat")>]
    let concat (regex1 : Regex) (regex2 : Regex) : Regex =
        // Create the Concat pattern, then simplify it before returning.
        simplifyRec (Concat (regex1, regex2)) id

    /// Conjunction of two regular expressions.
    /// This returns a new regular expression which matches an input string
    /// if and only if the input matches both of the given regular expressions.
    [<CompiledName("CreateAnd")>]
    let andr (regex1 : Regex) (regex2 : Regex) : Regex =
        // Create the Concat pattern, then simplify it before returning.
        simplifyRec (And (regex1, regex2)) id

    /// Disjunction of two regular expressions.
    /// This returns a new regular expression which matches an input string
    /// when the input matches either (or both) of the given regular expressions.
    [<CompiledName("CreateOr")>]
    let orr (regex1 : Regex) (regex2 : Regex) : Regex =
        // Create the Concat pattern, then simplify it before returning.
        simplifyRec (Or (regex1, regex2)) id

    /// Given two regular expressions, computes (regex1 / regex2).
    /// The resulting expression matches any string which matches regex1
    /// EXCEPT for those which also match regex2.
    [<CompiledName("Difference")>]
    let difference regex1 regex2 =
        regex2
        |> negate
        |> andr regex1


// Add derivative methods to Regex.
type Regex with
    /// Computes regex1 / regex2, given two regular expressions.
    /// The resulting expression matches any string which matches regex1
    /// EXCEPT for those which also match regex2.
    static member Difference (regex1, regex2) =
        Regex.difference regex1 regex2

    /// Recursively simplify a regular expression.
    /// The rewrite rules used to simplify the regular expression also try to normalize it;
    /// this, in turn, helps to minimize the number of states in the DFA which will
    /// eventually be generated for the expression.
    static member Simplify (regex : Regex) : Regex =
        // For the nullary patterns that can't be simplified, return immediately.
        // Otherwise, call the recursive implementation.
        match regex with
        | Epsilon
        | Any
        | CharacterSet _ ->
            regex
        | _ ->
            Regex.simplifyRec regex id

    /// <summary>
    /// Recursively simplify a regular expression.
    /// The rewrite rules used to simplify the regular expression also try to normalize it;
    /// this, in turn, helps to minimize the number of states in the DFA which will
    /// eventually be generated for the expression.
    /// </summary>
    /// <param name="regex"></param>
    /// <remarks>
    /// The result of this function should always be a non-null, non-empty sequence:
    /// the sequence will always contain at least the original input element.
    /// </remarks>
    static member SimplifySteps (regex : Regex) : seq<Regex> =
        // For the nullary patterns that can't be simplified, return immediately.
        // Otherwise, call the recursive implementation.
        match regex with
        | Epsilon
        | Any
        | CharacterSet _ ->
            Seq.singleton regex
        | _ ->
            // Produce a sequence of regexes representing the stepwise
            // simplification/normalization of the input regex.
            // Make sure that the first element of the returned sequence is always
            // the input element.
            seq {
            yield regex
            yield!
                // Using Seq.unfold here is a bit hacky since there's no real 'state'
                // value for the computation, but it works.
                regex
                |> Seq.unfold (fun regex ->
                    match Regex.simplifyStep regex id with
                    | None -> None
                    | Some simpRegex ->
                        Some (simpRegex, simpRegex))
            }

    /// Computes the derivative of a Regex with respect to a specified symbol.
    static member private DerivativeImpl wrtSymbol regex =
        cont {
        match regex with
        | Epsilon ->
            return Regex.empty

        | CharacterSet charSet ->
            return
                if CharSet.contains wrtSymbol charSet then
                    Regex.epsilon
                else
                    Regex.empty

        | Negate (CharacterSet charSet) ->
            return
                if CharSet.contains wrtSymbol charSet then
                    Regex.empty
                else
                    Regex.epsilon

        | Negate r ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            return Regex.negate r'

        | Star r ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            return Regex.concat r' regex

        | Concat (r, s) ->
            let ``nu(r)`` = if Regex.IsNullable r then Regex.epsilon else Regex.empty
            let! r' = Regex.DerivativeImpl wrtSymbol r
            let! s' = Regex.DerivativeImpl wrtSymbol s

            let or_r = Regex.concat r' s
            let or_s = Regex.concat ``nu(r)`` s'
            return Regex.orr or_r or_s

        | Or (r, s) ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            let! s' = Regex.DerivativeImpl wrtSymbol s
            return Regex.orr r' s'

        | And (r, s) ->
            let! r' = Regex.DerivativeImpl wrtSymbol r
            let! s' = Regex.DerivativeImpl wrtSymbol s
            return Regex.andr r' s'
        }

    /// Computes the derivative of a Regex with respect to a specified symbol.
    static member Derivative symbol regex =
        // OPTIMIZATION : Immediately return the result for some patterns instead of calling
        // the continuation-based method -- this eliminates the overhead of creating/calling
        // the continuations for some very common cases.
        match regex with
        | Epsilon ->
            Regex.empty

        | CharacterSet charSet ->
            if CharSet.contains symbol charSet then
                Regex.epsilon
            else
                Regex.empty

        | Negate (CharacterSet charSet) ->
            if CharSet.contains symbol charSet then
                Regex.empty
            else
                Regex.epsilon

        | _ ->
            Regex.DerivativeImpl symbol regex id
