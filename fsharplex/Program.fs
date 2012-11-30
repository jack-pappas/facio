(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpLex.Program

open Graph
open Nfa
open Regex

//
module internal AssemblyInfo =
    open System.Reflection
    open System.Resources
    open System.Runtime.CompilerServices
    open System.Runtime.InteropServices
    open System.Security
    open System.Security.Permissions

    [<assembly: AssemblyTitle("FSharpLex")>]
    [<assembly: AssemblyDescription("A 'lex'-inspired lexical-analyzer-generator tool for F#.")>]
    [<assembly: NeutralResourcesLanguage("en-US")>]
    [<assembly: Guid("3e878e31-5c9a-456d-9ab8-a12e3fed1efe")>]

    (*  Makes internal modules, types, and functions visible
        to the test project so they can be unit-tested. *)
    #if DEBUG
    [<assembly: InternalsVisibleTo("FSharpLex.Tests")>]
    #endif

    // Appease the F# compiler
    do ()

//// TEMP : Only needed to compute tables.
//open System.Collections.Generic
//open System.Globalization
//open SpecializedCollections
//
//let unicodeCategories =
//    let table = Dictionary<_,_> ()
//    for i = 0 to 65535 do
//        /// The Unicode category of this character.
//        let category = System.Char.GetUnicodeCategory (char i)
//
//        // Add this character to the set for this category.
//        table.[category] <-
//            match table.TryGetValue category with
//            | true, charSet ->
//                CharSet.add (char i) charSet
//            | false, _ ->
//                CharSet.singleton (char i)
//
//    // Convert the dictionary to a Map
//    (Map.empty, table)
//    ||> Seq.fold (fun categoryMap kvp ->
//        Map.add kvp.Key kvp.Value categoryMap)
//
//let unicodeCategoryRanges =
//    unicodeCategories
//    |> Map.map (fun _ charSet ->
//        charSet
//        |> CharSet.intervals
//        |> Seq.toArray)

open SpecializedCollections
open Regex

let testRegex =
    Regex.Or (
        Regex.Or (
            Regex.Character 'a',
            Regex.Concat (Regex.Character 'b', Regex.Character 'a')),
        Regex.Character 'c')

let testUniverse =
    CharSet.empty
    |> CharSet.addRange 'a' 'e'

let derivativeClasses =
    Regex.DerivativeClasses (testRegex, testUniverse)


printfn "Press any key to exit..."
System.Console.ReadKey ()
|> ignore

