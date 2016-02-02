(*

Copyright 2013-2014 Jack Pappas

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

/// Helper functions for implementing unit tests.
[<AutoOpen>]
module TestHelpers

open System
open System.Collections.Generic
open NUnit.Framework
open FsCheck


(* Fluent test helpers for use with NUnit and FsUnit. *)

/// Tests that the specified condition is true.
/// If not, calls Assert.Fail with a formatted string.
let inline assertf (condition : bool) format : 'T =
    Printf.ksprintf (fun str -> if not condition then Assert.Fail str) format

/// Asserts that two values are equal.
let inline assertEqual<'T when 'T : equality> (expected : 'T) (actual : 'T) =
    Assert.AreEqual (expected, actual)

/// Asserts that two values are NOT equal.
let inline assertNotEqual<'T when 'T : equality> (expected : 'T) (actual : 'T) =
    Assert.AreNotEqual (expected, actual)

/// Asserts that two objects are identical.
let inline assertSame<'T when 'T : not struct> (expected : 'T) (actual : 'T) =
    Assert.AreSame (expected, actual)

/// Asserts that two objects are NOT identical.
let inline assertNotSame<'T when 'T : not struct> (expected : 'T) (actual : 'T) =
    Assert.AreNotSame (expected, actual)

/// Asserts that a condition is true.
let inline assertTrue condition =
    Assert.IsTrue (condition)

/// Asserts that a condition is false.
let inline assertFalse condition =
    Assert.IsFalse (condition)


/// Assertion functions for collections.
[<RequireQualifiedAccess>]
module Collection =
    open System.Collections

    /// Asserts that two collections are exactly equal.
    /// The collections must have the same count, and contain the exact same objects in the same order.
    let inline assertEqual<'T, 'U when 'T :> seq<'U>> (expected : 'T) (actual : 'T) =
        CollectionAssert.AreEqual (expected, actual)

    /// Asserts that two collections are not exactly equal.
    let inline assertNotEqual<'T, 'U when 'T :> seq<'U>> (expected : 'T) (actual : 'T) =
        CollectionAssert.AreNotEqual (expected, actual)

    /// Asserts that two collections are exactly equal.
    /// The collections must have the same count, and contain the exact same objects but the match may be in any order.
    let inline assertEquiv<'T, 'U when 'T :> seq<'U>> (expected : 'T) (actual : 'T) =
        CollectionAssert.AreEquivalent (expected, actual)

    /// Asserts that two collections are not exactly equal.
    let inline assertNotEquiv<'T, 'U when 'T :> seq<'U>> (expected : 'T) (actual : 'T) =
        CollectionAssert.AreNotEquivalent (expected, actual)


(* Fluent test helpers for use with NUnit and FsCheck. *)

/// An FsCheck runner which reports FsCheck test results to NUnit.
type private NUnitRunner () =
    static let instance = NUnitRunner ()

    /// Default instance of the NUnitRunner class.
    static member Instance = instance

    interface IRunner with
        member __.OnStartFixture _ = ()
        member __.OnArguments (_,_,_) = ()
        member __.OnShrink (_,_) = ()
        member __.OnFinished (name, result) =
            match result with
            | TestResult.True (data, suppressResults) ->
                // TODO : Log the result data.
                Runner.onFinishedToString name result
                |> stdout.WriteLine

            | TestResult.Exhausted data ->
                // TODO : Log the result data.
                Runner.onFinishedToString name result
                |> Assert.Inconclusive

            | TestResult.False (_,_,_,_,_) ->
                // TODO : Log more information about the test failure.
                Runner.onFinishedToString name result
                |> Assert.Fail

/// An FsCheck configuration which logs test results to NUnit.
let private nUnitConfig verbose maxTest =
    let config = if verbose then Config.Verbose else Config.Quick
    { config with
        MaxTest = defaultArg maxTest 5000;
        Runner = NUnitRunner.Instance; }

//
let private defaultNUnitConfig =
    nUnitConfig false (Some 5000)

/// Tests that the specified property is correct.
let assertProp testName (property : 'Testable) =
    Check.One (testName, defaultNUnitConfig, property)

/// Tests that the specified property is correct.
let assertPropN testName maxTest (property : 'Testable) =
    let config = nUnitConfig false (Some maxTest)
    Check.One (testName, config, property)

/// Helper functions for implementing "journaled" FsCheck tests. These functions wrap
/// FsCheck with additional logic to record the generated inputs to a file before
/// running the property assertions. For cases where the property assertion raises a
/// StackOverflowException and crashes the test runner process, this makes it possible
/// to discover which input caused the crash.
[<RequireQualifiedAccess>]
module FsCheckJournaled =
    open System
    open System.IO

    /// Writes a line containing a tab-separated key/value pair to a TextWriter.
    let private writeTabSepKeyValue (textWriter : TextWriter) (key : string) (value : string) =
        textWriter.Write key
        textWriter.Write '\t'
        textWriter.WriteLine value

    /// Journaling version of 'assertProp'.
    /// Journaling is disabled if 'journalFile' is None.
    /// If the test does not crash, the file is deleted afterward; otherwise, the file will be
    /// left in place on the desktop and will contain the test case causing the crash.
    let assertProp (journalFile : string option) testName (serializer : TextWriter -> 'T -> unit) (predicate : 'T -> bool) =
        match journalFile with
        | None -> ()
        | Some journalFile ->
            eprintfn "Facio test journaling enabled. JournalFile = %s" journalFile

        assertProp testName <| fun (input : 'T) ->
            match journalFile with
            | None -> ()
            | Some journalFile ->
                // Create the journal file to hold the generated input.
                // If the file already exists, it's overwritten.
                use sw = new StreamWriter (journalFile)

                // Write the date/time and the test name.
                writeTabSepKeyValue sw "Date" (DateTime.UtcNow.ToString("o"))
                writeTabSepKeyValue sw "TestName" testName
                sw.WriteLine ()

                // Write the input to the journal file using the specified serializer.
                serializer sw input

            // Apply the predicate to the input.
            predicate input

        // If we reach this point, the test succeeded.
        // If running in journaling mode delete the journal since it's not needed (because the test passed).
        journalFile |> Option.iter File.Delete

    /// Journaling version of 'assertPropN'.
    /// Journaling is disabled if 'journalFile' is None.
    /// If the test does not crash, the file is deleted afterward; otherwise, the file will be
    /// left in place on the desktop and will contain the test case causing the crash.
    let assertPropN (journalFile : string option) testName maxTest (serializer : TextWriter -> 'T -> unit) (predicate : 'T -> bool) =
        match journalFile with
        | None -> ()
        | Some journalFile ->
            eprintfn "Facio test journaling enabled. JournalFile = %s" journalFile

        assertPropN testName maxTest <| fun (input : 'T) ->
            match journalFile with
            | None -> ()
            | Some journalFile ->
                // Create the journal file to hold the generated input.
                // If the file already exists, it's overwritten.
                use sw = new StreamWriter (journalFile)

                // Write the date/time and the test name.
                writeTabSepKeyValue sw "Date" (DateTime.UtcNow.ToString("o"))
                writeTabSepKeyValue sw "TestName" testName
                sw.WriteLine ()

                // Write the input to the journal file using the specified serializer.
                serializer sw input

            // Apply the predicate to the input.
            predicate input

        // If we reach this point, the test succeeded.
        // If running in journaling mode delete the journal since it's not needed (because the test passed).
        journalFile |> Option.iter File.Delete
