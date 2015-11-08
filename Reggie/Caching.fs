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

open Reggie.SpecializedCollections


/// <summary>
/// A set of derivative classes.
/// A 'derivative class' is a set of characters labeling a transition edge from one DFA state to another,
/// so <see cref="DerivativeClasses"/> is a set of character sets. It could be represented in F# as <c>Set{Set{char}}</c>,
/// but this representation uses a <see cref="HashSet{T}"/> of <see cref="CharSet"/>s, because <see cref="CharSet"/>
/// is a very efficient representation of dense character sets.
/// </summary>
type DerivativeClasses = HashSet<CharSet>

/// Caches the results of some "expensive" calculations performed during the compilation process to avoid repeating them.
type CompilationCache = {
    /// A cache used for hash-consing of CharSets.
    /// This is critical for performance; without it, definitions which make heavy use of Unicode character sets
    /// cause Reggie to spend a significant amount of time comparing CharSets for equality.
    /// With this cache, many of those equality checks are reduced to reference (physical) equality comparisons.
    CharSetCache : HashMap<CharSet, CharSet>;
    /// Caches the derivative of a regular expression with respect to a symbol.
    RegexDerivativeCache : HashMap<Regex, Map<char, Regex>>;
    /// Caches the set of derivative classes for a regular expression.
    DerivativeClassesCache : HashMap<Regex, DerivativeClasses>;
    /// Caches the intersection of two derivative classes.
    /// The intersection operation is commutative, so the derivative classes are sorted when creating the cache key
    /// to increase the cache hit ratio. The "lesser" key is used as the outer key.
    DerivativeClassIntersectionCache : HashMap<DerivativeClasses, HashMap<DerivativeClasses, DerivativeClasses>>;
}

/// <summary>Functions operating on <see cref="T:CompilationCache"/> instances.</summary>
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module CompilationCache =
    open ExtCore.Control.Collections

    /// Returns an empty CompilationCache instance.
    [<CompiledName("Empty")>]
    let empty =
        { CharSetCache = HashMap.empty;
          RegexDerivativeCache = HashMap.empty;
          DerivativeClassesCache = HashMap.empty;
          DerivativeClassIntersectionCache = HashMap.empty; }

    /// <summary>
    /// Interns a character set (<see cref="T:CharSet"/>) in the given compilation cache. If the cache does not already contain an
    /// equivalent character set, the set is added to the cache and returned along with the updated cache; otherwise, the equivalent set
    /// is returned along with the cache.
    /// In other words, this function hash-conses the character set using the compilation cache, which improves performance since
    /// equality checks between sets are reduced to physical equality checks.
    /// </summary>
    /// <param name="charSet"></param>
    /// <param name="compilationCache"></param>
    /// <returns></returns>
    [<CompiledName("InternCharSet")>]
    let internCharSet (charSet : CharSet) (compilationCache : CompilationCache) =
        // Preconditions
        // TODO

        // Intern the given CharSet into the cache, if necessary.
        let charSetCache = compilationCache.CharSetCache
        match HashMap.tryFind charSet charSetCache with
        | Some cachedCharSet ->
            cachedCharSet, compilationCache
        | None ->
            // Add the CharSet instance to the cache, then update the compilation cache.
            let compilationCache =
                { compilationCache with
                    CharSetCache = HashMap.add charSet charSet charSetCache }

            charSet, compilationCache

    /// <summary>
    /// </summary>
    /// <param name="derivativeClasses"></param>
    /// <param name="compilationCache"></param>
    /// <returns></returns>
    [<CompiledName("InternDerivativeClasses")>]
    let internDerivativeClasses (derivativeClasses : DerivativeClasses) (compilationCache : CompilationCache) : DerivativeClasses * _ =
        // Preconditions
        // TODO

        // Intern each CharSet instance in the given derivative class.
        // TODO : Also intern the actual DerivativeClasses (i.e., HashSet<CharSet>) instances? Would the perf. gain be worthwhile?
        State.HashSet.map internCharSet derivativeClasses compilationCache
