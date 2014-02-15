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

open ExtCore.Control
open ExtCore.Control.Collections

/// An array of regular expressions.
// Definition 4.3.
type RegularVector = Regex[]

/// Functional programming operators related to the RegularVector type.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module RegularVector =
    open LanguagePrimitives

    /// Compute the derivative of a regular vector with respect to the given symbol.
    /// The computation is memoized for increased performance.
    [<CompiledName("Derivative")>]
    let derivative symbol (regVec : RegularVector) (compilationCache : CompilationCache) : RegularVector * _ =
        // Preconditions
        // TODO

        /// The regular expression derivative cache.
        let regexDerivativeCache = compilationCache.RegexDerivativeCache

        // Compute the derivative of the regular vector w.r.t. the specified symbol.
        let regVec', regexDerivativeCache' =
            (regVec, regexDerivativeCache)
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

        // Update the compilation cache if necessary, then return the computed derivative
        // of the regular vector and the updated compilation cache.
        if regexDerivativeCache == regexDerivativeCache' then
            // No need to update the compilation cache.
            regVec', compilationCache
        else
            regVec', { compilationCache with RegexDerivativeCache = regexDerivativeCache' }

    /// Determines if the regular vector is nullable, i.e., it accepts the empty string (epsilon).
    [<CompiledName("IsNullable")>]
    let (*inline*) isNullable (regVec : RegularVector) =
        // A regular vector is nullable iff any of
        // the component regexes are nullable.
        Array.exists Regex.IsNullable regVec

    /// The indices of the element expressions (if any) that accept the empty string (epsilon).
    // OPTIMIZE : Return an IntSet (from ExtCore) instead of Set<int>.
    [<CompiledName("AcceptingElements")>]
    let acceptingElements (regVec : RegularVector) =
        // Find the indices of the expressions accepting the empty string.
        (Set.empty, regVec)
        ||> Array.foldi (fun accepting i regex ->
            if Regex.IsNullable regex then
                Set.add i accepting
            else
                accepting)

    /// Determines if a regular vector is an 'empty' vector.
    /// Note that an empty regular vector is *not* the same thing as an empty array.
    [<CompiledName("IsEmpty")>]
    let (*inline*) isEmpty (regVec : RegularVector) =
        // A regular vector is empty iff all of it's entries
        // are equal to the empty character set.
        Array.forall Regex.isEmpty regVec

    /// Compute the approximate set of derivative classes of a regular vector.
    /// The computation is memoized for increased performance.
    [<CompiledName("DerivativeClasses")>]
    let derivativeClasses (regVec : RegularVector) (compilationCache : CompilationCache) : DerivativeClasses * _ =
        // Preconditions
        if Array.isEmpty regVec then
            invalidArg "regVec" "The regular vector does not contain any regular expressions."

        (* Compute the approximate set of derivative classes for each regular expression in the vector.
           By Definition 4.3, the approximate set of derivative classes of a regular vector
           is the intersection of the approximate sets of derivative classes of it's elements. *)

        //
        let regVecDerivativeClasses, compilationCache =
            State.Array.map DerivativeClasses.ofRegex regVec compilationCache

        let zerothElement = regVecDerivativeClasses.[0]
        let regVecLen = Array.length regVec
        if regVecLen = 1 then
            zerothElement, compilationCache
        else
            let rest = ArrayView.create regVecDerivativeClasses 1 (regVecLen - 1)

            // TODO : Replace with State.ArrayView.fold, or better yet, State.ArrayView.reduce
            ((zerothElement, compilationCache), rest)
            ||> ArrayView.fold (fun (intersection, compilationCache) derivClass ->
                // Compute the intersection of this DerivativeClasses and the intersection of the previous DerivativeClasses.
                DerivativeClasses.intersect intersection derivClass compilationCache)
