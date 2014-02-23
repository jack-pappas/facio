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

namespace FSharpLex

open System.Diagnostics
open ExtCore.Control.Cps
open ExtCore.Control.Collections
open FSharpLex.SpecializedCollections

(*  Turn off warning about uppercase variable identifiers; some variables
    in the code below are are named using the F# backtick syntax so they
    can use names which closely match those in the paper. *)
#nowarn "49"


/// <summary>A regular expression.</summary>
/// <remarks>This type includes some cases which are normally referred to as "extended"
/// regular expressions. However, only those cases which are still closed under boolean
/// operations are included here, so the lanugage it represents must still be a regular
/// language.</remarks>
[<DebuggerDisplay("{DebuggerDisplay,nq}")>]
type Regex =
    /// The empty string.
    | Epsilon

    /// A set of characters.
    | CharacterSet of CharSet
    /// Negation.
    | Negate of Regex

    /// Kleene *-closure.
    /// The specified Regex will be matched zero (0) or more times.
    | Star of Regex
    /// Concatenation. A Regex immediately followed by another Regex.
    | Concat of Regex * Regex
    /// Choice between two regular expressions (i.e., boolean OR).
    | Or of Regex * Regex
    /// Boolean AND of two regular expressions.
    | And of Regex * Regex

    /// Infrastructure. Only for use with DebuggerDisplayAttribute.
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private this.DebuggerDisplay
        with get () =
            match this with
            | Epsilon ->
                "\u03f5"    // Epsilon symbol
            | CharacterSet charSet
                when CharSet.isEmpty charSet ->
                "{}"
            | CharacterSet charSet ->
                let sb = System.Text.StringBuilder ()
                sb.Append "{" |> ignore

                // Write each of the intervals into the StringBuilder.
                charSet
                |> CharSet.iterIntervals (fun lo hi ->
                    Printf.bprintf sb "\u%04x-\u%04x, " (int lo) (int hi))

                sb.Length <- sb.Length - 2  // Remove the trailing ", "
                sb.Append "}" |> ignore

                sb.ToString ()

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

    // TODO : Implement a method for checking equivalence of two regular expressions?
    //        This is possible for regular expressions, but is it possible for extended regular expressions?


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
        | CharacterSet charSet ->
            CharSet.isEmpty charSet
        | _ ->
            false

    /// Partial active pattern which may be used to detect the 'empty' language.
    let inline private (|Empty|_|) regex =
        match regex with
        | CharacterSet charSet
            when CharSet.isEmpty charSet ->
            Some ()
        | _ ->
            None

    /// Partial active pattern which may be used to detect a pattern which matches one (1) instance of any character.
    let inline private (|Any|_|) regex =
        match regex with
        | Negate Empty ->
            Some ()
        | _ ->
            None

    /// Returns a new regular expression which matches exactly one (1) instance of the specified character.
    [<CompiledName("OfCharacter")>]
    let inline ofChar c =
        CharacterSet <| CharSet.singleton c

    /// Returns a new regular expression which matches exactly one (1) instance
    /// of any character in the specified set.
    [<CompiledName("OfCharSet")>]
    let inline ofCharSet (set : CharSet) : Regex =
        CharacterSet set

    //
    let rec private simplify regex =
        cont {
        match regex with
        | Epsilon
        | Any
        | CharacterSet _ ->
            return regex

        (* Negate *)
        // Double-negation cancels out.
        | Negate (Negate regex) ->
            return! simplify regex
        | Negate regex ->
            // Simplify the inner regex first.
            let! regex = simplify regex
            match regex with
            | Epsilon ->
                return empty

            // Use DeMorgan's rules to simplify negation of Or and And patterns when possible.
            // This isn't specified in the original paper, but it helps to compact the regex.
            | Or (regex1, regex2) ->
                return! simplify <| And (regex1, regex2)
            | And (regex1, regex2) ->
                return! simplify <| Or (regex1, regex2)

            // Double-negation cancels out.
            | Negate regex ->
                // 'regex' is already simplified, so it can be returned without simplifying again.
                return regex

            | _ ->
                return Negate regex

        (* Star *)
        // The Star operation is idempotent -- nested Stars are equivalent to a single Star.
        | Star (Star regex) ->
            return! simplify <| Star regex
        | Star regex ->
            // Simplify the inner regex first.
            let! regex = simplify regex
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
            return! simplify <| Concat (r, Concat (s, t))
        | Concat (regex1, regex2) ->
            // Simplify the two sub-regexes first.
            let! regex1 = simplify regex1
            let! regex2 = simplify regex2

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
                return! simplify <| Concat (r, Concat (s, t))

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
        // Nested And patterns should skew towards the left.
        | And (r, And (s, t)) ->
            return! simplify <| And (And (r, s), t)
        | And (regex1, regex2) ->
            // Simplify the two sub-regexes first.
            let! regex1 = simplify regex1
            let! regex2 = simplify regex2

            match regex1, regex2 with
            | Empty, _
            | _, Empty ->
                return empty

            | Any, regex
            | regex, Any ->
                return regex

            // TODO : Should we have rules for And (Epsilon, _) and And (_, Epsilon)?

            // Nested And patterns should skew towards the left.
            | r, And (s, t) ->
                return! simplify <| And (And (r, s), t)

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

//            | CharacterSet positiveSet, Negate (CharacterSet negativeSet)
//            | Negate (CharacterSet negativeSet), CharacterSet positiveSet ->
//                return! notImpl ""

            // NOTE : These next two rewrite rules aren't specified in the original paper,
            //        but are useful for keeping the regex compact in certain cases.
            | Star (CharacterSet charSet1), Star (CharacterSet charSet2) ->
                // No simplification needed for Star (CharacterSet _), so just return it.
                return
                    CharSet.intersect charSet1 charSet2
                    |> CharacterSet
                    |> Star

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
        // Nested Or patterns should skew towards the left.
        | Or (r, Or (s, t)) ->
            return! simplify <| Or (Or (r, s), t)
        | Or (regex1, regex2) ->
            // Simplify the two sub-regexes first.
            let! regex1 = simplify regex1
            let! regex2 = simplify regex2

            match regex1, regex2 with
            | Empty, regex
            | regex, Empty ->
                // 'regex' is already simplified, so we can just return it.
                return regex

            | Any, _
            | _, Any ->
                return any

            // Nested Or patterns should skew towards the left.
            | r, Or (s, t) ->
                return! simplify <| Or (Or (r, s), t)

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
        simplify (Star regex) id

    /// Creates a normalized Regex.Negate from the specified Regex.
    [<CompiledName("CreateNegate")>]
    let negate (regex : Regex) : Regex =
        // Create the Negate pattern, then simplify it before returning.
        simplify (Negate regex) id

    /// Concatenates two regular expressions so they'll be matched sequentially.
    [<CompiledName("CreateConcat")>]
    let concat (regex1 : Regex) (regex2 : Regex) : Regex =
        // Create the Concat pattern, then simplify it before returning.
        simplify (Concat (regex1, regex2)) id

    /// Conjunction of two regular expressions.
    /// This returns a new regular expression which matches an input string
    /// if and only if the input matches both of the given regular expressions.
    [<CompiledName("CreateAnd")>]
    let andr (regex1 : Regex) (regex2 : Regex) : Regex =
        // Create the Concat pattern, then simplify it before returning.
        simplify (And (regex1, regex2)) id

    /// Disjunction of two regular expressions.
    /// This returns a new regular expression which matches an input string
    /// when the input matches either (or both) of the given regular expressions.
    [<CompiledName("CreateOr")>]
    let orr (regex1 : Regex) (regex2 : Regex) : Regex =
        // Create the Concat pattern, then simplify it before returning.
        simplify (Or (regex1, regex2)) id

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
