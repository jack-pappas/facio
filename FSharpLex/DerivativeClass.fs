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

open ExtCore.Control.Cps
open ExtCore.Control.Collections
open ExtCore.Control.Collections.Cps
open FSharpLex.SpecializedCollections

(*  Turn off warning about uppercase variable identifiers;
    some variables in the code below are named using the
    F# backtick syntax so they can use names which closely
    match those in the paper. *)
#nowarn "49"


//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module DerivativeClasses =
    open ExtCore.Control

    //
    [<CompiledName("Universe")>]
    let universe : DerivativeClasses =
        HashSet.singleton CharSet.universe

    //
    [<CompiledName("OfCharSet")>]
    let ofCharSet charSet : DerivativeClasses =
        HashSet.empty
        |> HashSet.add charSet
        |> HashSet.add (CharSet.complement charSet)

    /// Computes a conservative approximation of the intersection of two sets of derivative classes.
    /// This is needed when computing the set of derivative classes for a compound regular expression ('And', 'Or', and 'Concat').
    [<CompiledName("Intersect")>]
    let intersect (``C(r)`` : DerivativeClasses) (``C(s)`` : DerivativeClasses) (compilationCache : CompilationCache) : DerivativeClasses * _ =
        // Preconditions
        // TODO

        // Intern the derivative classes first.
        let ``C(r)``, compilationCache = CompilationCache.internDerivativeClasses ``C(r)`` compilationCache
        let ``C(s)``, compilationCache = CompilationCache.internDerivativeClasses ``C(s)`` compilationCache

        // Sort the derivative classes -- the intersection operation is commutative, so (f x y) = (f y x).
        // By sorting the two derivative classes here, we increase the cache hit ratio (and also reduce the size of the cache).
        let ``C(r)``, ``C(s)`` =
            if ``C(r)`` < ``C(s)`` then ``C(r)``, ``C(s)``
            else ``C(s)``, ``C(r)``

        // Does this intersection already exist in the cache?
        let intersection =
            compilationCache.DerivativeClassIntersectionCache
            |> HashMap.tryFind ``C(r)``
            |> Option.bind (fun innerMap ->
                innerMap
                |> HashMap.tryFind ``C(s)``)

        match intersection with
        | Some intersection ->
            intersection, compilationCache
        | None ->
            //
            let intersection, compilationCache =
                // Compute the intersection of each set in the Cartesian product of the derivative classes.
                (HashSet.empty, ``C(r)``, compilationCache)
                |||> State.HashSet.fold (fun intersections cr compilationCache ->
                    (intersections, ``C(s)``, compilationCache)
                    |||> State.HashSet.fold (fun intersections cs ->
                        state {
                        // Does this intersection already exist in the cache?
                        //let! compilationCache = State.getState
                        //match HashMap.tryFind cr compilationCache.

                        let! intersection =
                            // Compute the intersection.
                            CharSet.intersect cr cs
                            // Intern the intersection.
                            |> CompilationCache.internCharSet

                        return HashSet.add intersection intersections
                        }))

            // Add the intersection to the compilation cache.
            let intersectionCache =
                let intersectionCache = compilationCache.DerivativeClassIntersectionCache
                match HashMap.tryFind ``C(r)`` intersectionCache with
                | None ->
                    HashMap.add ``C(r)`` (HashMap.singleton ``C(s)`` intersection) intersectionCache
                | Some cache ->
                    HashMap.add ``C(r)`` (HashMap.add ``C(s)`` intersection cache) intersectionCache

            // Return the intersection and the updated compilation cache.
            intersection, { compilationCache with DerivativeClassIntersectionCache = intersectionCache }

    /// Computes an approximate set of derivative classes for the specified Regex.
    let rec private ofRegexImpl regex =
        stateCont {
        match regex with
        | Epsilon ->
            return universe
        | Negate (CharacterSet charSet)     // Any
            when CharSet.isEmpty charSet ->
            return universe

        | _ ->
            let! compilationCache = StateCont.getState
            match HashMap.tryFind regex compilationCache.DerivativeClassesCache with
            | Some derivativeClasses ->
                return derivativeClasses
            | None ->
                let! derivativeClasses =
                    stateCont {
                    match regex with
                    | Epsilon ->
                        return universe
                    | CharacterSet charSet ->
                        return ofCharSet charSet
                    | Negate r
                    | Star r ->
                        return! ofRegexImpl r
                    | Concat (r, s) ->
                        if not <| Regex.IsNullable r then
                            return! ofRegexImpl r
                        else
                            let! ``C(r)`` = ofRegexImpl r
                            let! ``C(s)`` = ofRegexImpl s

                            // TODO : Clean this up -- we shouldn't have to extract and set the state manually here.
                            let! compilationState = StateCont.getState
                            let intersection, compilationState = intersect ``C(r)`` ``C(s)`` compilationState
                            do! StateCont.setState compilationState
                            return intersection
                    | Or (r, s)
                    | And (r, s) ->
                        let! ``C(r)`` = ofRegexImpl r
                        let! ``C(s)`` = ofRegexImpl s

                        // TODO : Clean this up -- we shouldn't have to extract and set the state manually here.
                        let! compilationState = StateCont.getState
                        let intersection, compilationState = intersect ``C(r)`` ``C(s)`` compilationState
                        do! StateCont.setState compilationState
                        return intersection
                        }

                // Get the compilation cache again (in case it was modified when recursively traversing the child nodes).
                let! compilationCache = StateCont.getState
                match HashMap.tryFind regex compilationCache.DerivativeClassesCache with
                | Some derivativeClasses ->
                    return derivativeClasses
                | None ->
                    // Add the set of derivative classes to the cache before returning.
                    let derivativeClassesCache = HashMap.add regex derivativeClasses compilationCache.DerivativeClassesCache
                    do! StateCont.setState { compilationCache with DerivativeClassesCache = derivativeClassesCache }
                    return derivativeClasses
        }

    /// Computes an approximate set of derivative classes for the specified Regex.
    [<CompiledName("FromRegex")>]
    let ofRegex (regex : Regex) (compilationCache : CompilationCache) =
        // OPTIMIZATION :   For a few common patterns which always return the same set of derivative classes,
        //                  avoid the cache lookup -- just return the result immediately.
        match regex with
        | Epsilon ->
            universe, compilationCache
        | _ ->
            // Try to find the set of derivative classes for this Regex in the cache;
            // if they're not present in the cache, compute the set and add it to the cache before returning.
            match HashMap.tryFind regex compilationCache.DerivativeClassesCache with
            | Some derivativeClasses ->
                derivativeClasses, compilationCache
            | None ->
                match regex with
                | Epsilon ->
                    // Shouldn't ever hit this (because we've already matched these patterns earlier)
                    // but we might as well include them here for completeness.
                    universe, compilationCache

                | _ ->
                    // Compute the set of derivative classes for this regex.
                    ofRegexImpl regex compilationCache id
