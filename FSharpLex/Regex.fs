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
module FSharpLex.Regex

open System.Diagnostics
open LanguagePrimitives
open ExtCore
open ExtCore.Collections
open ExtCore.Control.Cps
open ExtCore.Control.Collections
open FSharpLex.SpecializedCollections

(*  Turn off warning about uppercase variable identifiers;
    some variables in the code below are named using the
    F# backtick syntax so they can use names which closely
    match those in the paper. *)
#nowarn "49"


//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module DerivativeClass =
    //
    [<CompiledName("Universe")>]
    let universe =
        CharSet.ofRange System.Char.MinValue System.Char.MaxValue

    //
    [<CompiledName("Complement")>]
    let complement derivClass =
        CharSet.difference universe derivClass

//
type DerivativeClasses = HashSet<CharSet>

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module DerivativeClasses =
    //
    [<CompiledName("Universe")>]
    let universe : DerivativeClasses =
        HashSet.singleton DerivativeClass.universe

    //
    [<CompiledName("OfCharSet")>]
    let ofCharSet charSet : DerivativeClasses =
        HashSet.empty
        |> HashSet.add charSet
        |> HashSet.add (DerivativeClass.complement charSet)

    /// Computes a conservative approximation of the intersection of two sets of
    /// derivative classes. This is needed when computing the set of derivative
    /// classes for a compound regular expression ('And', 'Or', and 'Concat').
    [<CompiledName("Intersect")>]
    let intersect ``C(r)`` ``C(s)`` : DerivativeClasses =
        //Set.Cartesian.map CharSet.intersect ``C(r)`` ``C(s)``
        (HashSet.empty, ``C(r)``)
        ||> HashSet.fold (fun intersections cr ->
            (intersections, ``C(s)``)
            ||> HashSet.fold (fun intersections cs ->
                let intersection = CharSet.intersect cr cs
                HashSet.add intersection intersections))


/// <summary>A regular expression.</summary>
/// <remarks>This type includes some cases which are normally referred to as "extended"
/// regular expressions. However, only those cases which are still closed under boolean
/// operations are included here, so the lanugage it represents must still be a regular
/// language.</remarks>
[<DebuggerDisplay("{DebuggerDisplay,nq}")>]
type Regex =
    /// The empty string.
    | Epsilon
    /// Any character.
    | Any

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
                "Empty"
            | CharacterSet charSet
                when CharSet.count charSet = 1 ->
                let c = CharSet.minElement charSet
                c.ToString ()
            | regex ->
                // TODO : Finish this for the other regex cases.
                // It would be nice if this would print the regex in usual printed form.
                sprintf "%A" regex

    /// Determines if a specified Regex is 'nullable',
    /// i.e., it accepts the empty string (epsilon).
    static member private IsNullableImpl regex =
        cont {
        match regex with
        | Epsilon
        | Star _ ->
            return true
        | Any
        | CharacterSet _ ->
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
        | Any
        | CharacterSet _ ->
            false
        | _ ->
            Regex.IsNullableImpl regex id


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

    /// The regular expression which matches exactly one (1) instance of any character.
    [<CompiledName("Any")>]
    let any : Regex =
        Any

    /// The regular expression which never matches (accepts) anything.
    [<CompiledName("Empty")>]
    let empty : Regex =
        CharacterSet CharSet.empty

    /// Is the regular expression empty?
    [<CompiledName("IsEmpty")>]
    let isEmpty regex =
        match regex with
        | CharacterSet charSet ->
            CharSet.isEmpty charSet
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

    /// Creates a normalized Regex.Negate from the specified Regex.
    [<CompiledName("CreateNegate")>]
    let rec negate (regex : Regex) : Regex =
        match regex with
        | Negate (Negate regex) ->
            negate regex
        | Negate regex ->
            regex
        | _ ->
            Negate regex

    /// Returns a new regular expression which matches the given
    /// regular expression zero or more times.
    [<CompiledName("CreateStar")>]
    let rec star (regex : Regex) : Regex =
        match regex with
        | Epsilon ->
            Epsilon
        | CharacterSet charSet
            when CharSet.isEmpty charSet ->
            Epsilon
        | Or (Epsilon, regex)
        | Or (regex, Epsilon)
        | Star regex ->
            star regex
        | _ ->
            Star regex

    //
    let rec private concatImpl (regex1 : Regex) (regex2 : Regex) =
        cont {
        match regex1, regex2 with
        | regex, Epsilon
        | Epsilon, regex ->
            return regex
        | CharacterSet charSet, _
        | _, CharacterSet charSet
            when CharSet.isEmpty charSet ->
            return empty

        // Nested Concat patterns should skew towards the right.
        | Concat (r, s), t ->
            let! s' = concatImpl s t
            return! concatImpl r s'

        | _, _ ->
            return Concat (regex1, regex2)
        }

    /// Concatenates two regular expressions so they'll be matched sequentially.
    [<CompiledName("CreateConcat")>]
    let concat (regex1 : Regex) (regex2 : Regex) : Regex =
        // Call the recursive implementation.
        concatImpl regex1 regex2 id

    //
    let rec private andImpl (regex1 : Regex) (regex2 : Regex) =
        cont {
        match regex1, regex2 with
        | CharacterSet charSet, _
        | _, CharacterSet charSet
            when CharSet.isEmpty charSet ->
            return empty

        | CharacterSet charSet1, CharacterSet charSet2 ->
            return
                CharSet.intersect charSet1 charSet2
                |> CharacterSet

        | Any, regex
        | regex, Any ->
            return regex

        // Nested And patterns should skew towards the right.
        | And (r, s), t ->
            let! s' = andImpl s t
            return! andImpl r s'

        | _, _ ->
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
        }

    /// Conjunction of two regular expressions.
    /// This returns a new regular expression which matches an input string
    /// if and only if the input matches both of the given regular expressions.
    [<CompiledName("CreateAnd")>]
    let andr (regex1 : Regex) (regex2 : Regex) : Regex =
        // Call the recursive implementation.
        andImpl regex1 regex2 id

    //
    let rec private orImpl (regex1 : Regex) (regex2 : Regex) =
        cont {
        match regex1, regex2 with
        | CharacterSet charSet, regex
        | regex, CharacterSet charSet
            when CharSet.isEmpty charSet ->
            return regex

        | CharacterSet charSet1, CharacterSet charSet2 ->
            return
                CharSet.union charSet1 charSet2
                |> CharacterSet

        | Any, _
        | _, Any ->
            return Any

        // Nested Or patterns should skew towards the right.
        | Or (r, s), t ->
            let! s' = orImpl s t
            return! orImpl r s'

        | _, _ ->
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

    /// Disjunction of two regular expressions.
    /// This returns a new regular expression which matches an input string
    /// when the input matches either (or both) of the given regular expressions.
    [<CompiledName("CreateOr")>]
    let orr (regex1 : Regex) (regex2 : Regex) : Regex =
        // Call the recursive implementation.
        orImpl regex1 regex2 id

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
        | Any ->
            return Regex.epsilon

        | CharacterSet charSet ->
            return
                if CharSet.contains wrtSymbol charSet then
                    Regex.epsilon
                else
                    Regex.empty

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
        | Any ->
            Regex.epsilon

        | CharacterSet charSet ->
            if CharSet.contains symbol charSet then
                Regex.epsilon
            else
                Regex.empty

        | _ ->
            Regex.DerivativeImpl symbol regex id

    /// Computes an approximate set of derivative classes for the specified Regex.
    static member private DerivativeClassesImpl regex =
        stateCont {
        match regex with
        | Epsilon
        | Any ->
            return DerivativeClasses.universe

        | _ ->
            let! cache = StateCont.getState
            match HashMap.tryFind regex cache with
            | Some derivativeClasses ->
                return derivativeClasses
            | None ->
                let! derivativeClasses =
                    stateCont {
                    match regex with
                    | Epsilon
                    | Any ->
                        return DerivativeClasses.universe
                    | CharacterSet charSet ->
                        return DerivativeClasses.ofCharSet charSet
                    | Negate r
                    | Star r ->
                        return! Regex.DerivativeClassesImpl r
                    | Concat (r, s) ->
                        if not <| Regex.IsNullable r then
                            return! Regex.DerivativeClassesImpl r
                        else
                            let! ``C(r)`` = Regex.DerivativeClassesImpl r
                            let! ``C(s)`` = Regex.DerivativeClassesImpl s
                            return DerivativeClasses.intersect ``C(r)`` ``C(s)``
                    | Or (r, s)
                    | And (r, s) ->
                        let! ``C(r)`` = Regex.DerivativeClassesImpl r
                        let! ``C(s)`` = Regex.DerivativeClassesImpl s
                        return DerivativeClasses.intersect ``C(r)`` ``C(s)`` }

                // Add the set of derivative classes to the cache before returning.
                let cache = HashMap.add regex derivativeClasses cache
                do! StateCont.setState cache
                return derivativeClasses
        }

    /// Computes an approximate set of derivative classes for the specified Regex.
    static member DerivativeClasses (regex : Regex) (derivativeClassCache : HashMap<Regex, DerivativeClasses>) =
        // OPTIMIZATION :   For a few common patterns which always return the same set of derivative classes,
        //                  avoid the cache lookup -- just return the result immediately.
        match regex with
        | Epsilon
        | Any ->
            DerivativeClasses.universe, derivativeClassCache
        | _ ->
            // Try to find the set of derivative classes for this Regex in the cache;
            // if they're not present in the cache, compute the set and add it to the cache before returning.
            match HashMap.tryFind regex derivativeClassCache with
            | Some derivativeClasses ->
                derivativeClasses, derivativeClassCache
            | None ->
                match regex with
                | Epsilon
                | Any ->
                    // Shouldn't ever hit this (because we've already matched these patterns earlier)
                    // but we might as well include them here for completeness.
                    DerivativeClasses.universe, derivativeClassCache

                | _ ->
                    // Compute the set of derivative classes for this regex.
                    Regex.DerivativeClassesImpl regex derivativeClassCache id


/// An array of regular expressions.
// Definition 4.3.
type RegularVector = Regex[]

/// Functional programming operators related to the RegularVector type.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module RegularVector =
    open LanguagePrimitives

    /// Compute the derivative of a regular vector with respect to the given symbol.
    /// The computation is memoized for increased performance.
    let derivative symbol (regVec : RegularVector) (derivativeCache : HashMap<Regex, Map<char, Regex>>)
        : RegularVector * HashMap<Regex, Map<char, Regex>> =
        (regVec, derivativeCache)
        ||> State.Array.map (fun regex derivativeCache ->
            match HashMap.tryFind regex derivativeCache with
            | Some symbolMap ->
                match Map.tryFind symbol symbolMap with
                | Some regex' ->
                    regex', derivativeCache
                | None ->
                    let regex' = Regex.Derivative symbol regex
                    let symbolMap = Map.add symbol regex' symbolMap
                    let derivativeCache = HashMap.add regex symbolMap derivativeCache
                    regex', derivativeCache

            | None ->
                let regex' = Regex.Derivative symbol regex
                let symbolMap = Map.singleton symbol regex'
                let derivativeCache = HashMap.add regex symbolMap derivativeCache
                regex', derivativeCache
            )

    /// Determines if the regular vector is nullable,
    /// i.e., it accepts the empty string (epsilon).
    let (*inline*) isNullable (regVec : RegularVector) =
        // A regular vector is nullable iff any of
        // the component regexes are nullable.
        Array.exists Regex.IsNullable regVec

    /// The indices of the element expressions (if any)
    /// that accept the empty string (epsilon).
    // OPTIMIZE : Return an IntSet (from ExtCore) instead of Set<int>.
    let acceptingElements (regVec : RegularVector) =
        // Find the indices of the expressions accepting the empty string.
        (Set.empty, regVec)
        ||> Array.foldi (fun accepting i regex ->
            if Regex.IsNullable regex then
                Set.add i accepting
            else
                accepting)

    /// Determines if a regular vector is an empty vector. Note that an
    /// empty regular vector is *not* the same thing as an empty array.
    let (*inline*) isEmpty (regVec : RegularVector) =
        // A regular vector is empty iff all of it's entries
        // are equal to the empty character set.
        Array.forall Regex.isEmpty regVec

    /// Compute the approximate set of derivative classes of a regular vector.
    /// The computation is memoized for increased performance.
    let derivativeClasses (regVec : RegularVector) (derivativeClassCache : HashMap<Regex, DerivativeClasses>) (intersectionCache : HashMap<DerivativeClasses, HashMap<DerivativeClasses, DerivativeClasses>>)
        : DerivativeClasses * HashMap<Regex, DerivativeClasses> * HashMap<DerivativeClasses, HashMap<DerivativeClasses, DerivativeClasses>> =
        // Preconditions
        if Array.isEmpty regVec then
            invalidArg "regVec" "The regular vector does not contain any regular expressions."

        (* Compute the approximate set of derivative classes
           for each regular expression in the vector.
           By Definition 4.3, the approximate set of derivative classes
           of a regular vector is the intersection of the approximate
           sets of derivative classes of it's elements. *)

        // OPTIMIZE : Use State.Array.mapReduce from ExtCore so we can still cache the
        // results of the derivative-class intersections, but while describing the computation
        // in a parallelizable form.
        let regVecDerivativeClasses, derivativeClassCache =
            State.Array.map Regex.DerivativeClasses regVec derivativeClassCache

        let zerothElement = regVecDerivativeClasses.[0]
        let regVecLen = Array.length regVec
        if regVecLen = 1 then
            zerothElement, derivativeClassCache, intersectionCache
        else
            let rest = ArrayView.create regVecDerivativeClasses 1 (regVecLen - 1)
            ((zerothElement, derivativeClassCache, intersectionCache), rest)
            ||> ArrayView.fold (fun (intersection, derivativeClassesCache, intersectionCache) derivClass ->
                let key1, key2 =
                    if intersection < derivClass then intersection, derivClass
                    else derivClass, intersection

                // Try to find the intersection in the cache; if it's not found,
                // compute it then add it to the cache for later reuse.
                match HashMap.tryFind key1 intersectionCache with
                | Some cache2 ->
                    match HashMap.tryFind key2 cache2 with
                    | Some intersection ->
                        intersection, derivativeClassesCache, intersectionCache
                    | None ->
                        // Compute the intersection of this derivative class and the intersection
                        // of the previous derivative classes.
                        let intersection = DerivativeClasses.intersect intersection derivClass

                        // Add the result to the cache, then return it.
                        let cache2 = HashMap.add key2 intersection cache2
                        let intersectionCache = HashMap.add key1 cache2 intersectionCache
                        intersection, derivativeClassesCache, intersectionCache

                | None ->
                    // Compute the intersection of this derivative class and the intersection
                    // of the previous derivative classes.
                    let intersection = DerivativeClasses.intersect intersection derivClass

                    // Add the result to the cache, then return it.
                    let cache2 = HashMap.singleton key2 intersection
                    let intersectionCache = HashMap.add key1 cache2 intersectionCache
                    intersection, derivativeClassesCache, intersectionCache)
