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
    let intersect (``C(r)`` : DerivativeClasses) (``C(s)`` : DerivativeClasses) : DerivativeClasses =
        //Set.Cartesian.map CharSet.intersect ``C(r)`` ``C(s)``
        (HashSet.empty, ``C(r)``)
        ||> HashSet.fold (fun intersections cr ->
            (intersections, ``C(s)``)
            ||> HashSet.fold (fun intersections cs ->
                let intersection = CharSet.intersect cr cs
                HashSet.add intersection intersections))

    //
    [<CompiledName("Intern")>]
    let intern (derivativeClasses : DerivativeClasses) (charSetCache : HashMap<CharSet, CharSet>) : DerivativeClasses * _ =
        (derivativeClasses, charSetCache)
        ||> State.HashSet.map (fun derivativeClass charSetCache ->
            match HashMap.tryFind derivativeClass charSetCache with
            | Some cachedDerivativeClass ->
                cachedDerivativeClass, charSetCache
            | None ->
                // Add the derivative class (a CharSet) to the cache.
                let charSetCache = HashMap.add derivativeClass derivativeClass charSetCache
                derivativeClass, charSetCache)

    /// Computes an approximate set of derivative classes for the specified Regex.
    let rec private ofRegexImpl regex =
        stateCont {
        match regex with
        | Epsilon
        | Any ->
            return universe

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
                            return intersect ``C(r)`` ``C(s)``
                    | Or (r, s)
                    | And (r, s) ->
                        let! ``C(r)`` = ofRegexImpl r
                        let! ``C(s)`` = ofRegexImpl s
                        return intersect ``C(r)`` ``C(s)`` }

                // Add the set of derivative classes to the cache before returning.
                let cache = HashMap.add regex derivativeClasses cache
                do! StateCont.setState cache
                return derivativeClasses
        }

    /// Computes an approximate set of derivative classes for the specified Regex.
    [<CompiledName("FromRegex")>]
    let ofRegex (regex : Regex) (derivativeClassCache : HashMap<Regex, DerivativeClasses>) =
        // OPTIMIZATION :   For a few common patterns which always return the same set of derivative classes,
        //                  avoid the cache lookup -- just return the result immediately.
        match regex with
        | Epsilon
        | Any ->
            universe, derivativeClassCache
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
                    universe, derivativeClassCache

                | _ ->
                    // Compute the set of derivative classes for this regex.
                    ofRegexImpl regex derivativeClassCache id

