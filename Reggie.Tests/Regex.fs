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

namespace Tests.Reggie

open Reggie
open Reggie.SpecializedCollections
open NUnit.Framework
open FsCheck


/// Tests for the Regex type and module.
module RegexTests =
    [<Test>]
    let ``difference of CharSet regex with itself is the null language`` () : unit =
        // Create a CharacterSet regex for the low ASCII characters.
        let charSetRegex = Regex.CharacterSet (CharSet.ofRange (char 0) (char 127))

        // Take difference of the regex and itself.
        let diff = Regex.Difference (charSetRegex, charSetRegex)

        // The resulting regex should be the null language.
        diff
        |> assertEqual Regex.empty

    [<Test(Description =
        "Check whether Regex.Simplify terminates for doubly-nested And patterns.")>]
    let ``simplify terminates for doubly-nested And patterns`` () : unit =
        let inputRegex = And (And (Epsilon,Epsilon),And (Epsilon,Epsilon))

        // Try to simplify the input regex.
        let simplifiedRegex = Regex.Simplify inputRegex

        // If Regex.Simplify returned, it didn't get stuck in infinite recursion.
        Assert.Pass ()

    [<Test(Description =
        "Check whether Regex.Simplify terminates for doubly-nested Or patterns.")>]
    let ``simplify terminates for doubly-nested Or patterns`` () : unit =
        let inputRegex = Or (Or (Epsilon,Epsilon),Or (Epsilon,Epsilon))

        // Try to simplify the input regex.
        let simplifiedRegex = Regex.Simplify inputRegex

        // If Regex.Simplify returned, it didn't get stuck in infinite recursion.
        Assert.Pass ()

    /// Contains data for a Regex.Simplify test case.
    type private RegexSimplifyTestCase = {
        Description : string option;
        Name : string option;
        Regex : Regex;
        KnownFailure : bool;
    } with
        /// Create a TestCaseData instance from a RegexSimplifyTestCase record.
        static member ToTestCaseData testCase =
            let mutable result = TestCaseData(testCase.Regex)

            match testCase.Name with
            | None -> ()
            | Some name ->
                result <- result.SetName name

            match testCase.Description with
            | None -> ()
            | Some desc ->
                result <- result.SetDescription desc

            if testCase.KnownFailure then
                result.Ignore ("This test case is known to be failing.")
            else
                result

        /// Create a TestCaseData instance from a RegexSimplifyTestCase record.
        static member ToTestCaseData (testCaseIndex, testCase) =
            let testCase =
                match testCase.Name with
                | Some _ ->
                    testCase
                | None ->
                    // Fill in the name using the test case index.
                    let name = sprintf "Regex.Simplify #%i" testCaseIndex
                    { testCase with Name = Some name }

            RegexSimplifyTestCase.ToTestCaseData testCase

    /// Test case source for Regex.Simplify tests.
    [<Sealed>]
    type private RegexSimplifyTestCases () =
        /// Create a RegexSimplifyTestCase record from a Regex.
        static let regexCase regex =
            { Regex = regex; Name = None; Description = None; KnownFailure = false; }

        /// Create a RegexSimplifyTestCase record from a Regex.
        /// The test case will be ignored (not run) but will still show in up the test runner.
        static let regexCaseBroken regex =
            { Regex = regex; Name = None; Description = None; KnownFailure = true; }

        member __.RawItems () =
            seq {
            yield regexCase <|
                And (CharacterSet (CharSet.ofRange '\u0056' '\u0056'), And (Epsilon, Epsilon))
            yield regexCase <|
                And (CharacterSet (CharSet.ofRange '\u0037' '\u0037'), And (Epsilon, Concat (Epsilon, Epsilon)))
            yield regexCase <|
                And (CharacterSet (CharSet.ofRange '\u0037' '\u0037'), Epsilon)
            yield regexCase <|
                Or (Epsilon, Or (Star Epsilon, CharacterSet (CharSet.OfIntervals [| '\u0042', '\u0042'; '\u004c', '\u004c' |])))
            yield regexCase <|
                And (Epsilon, And (Epsilon, CharacterSet (CharSet.OfIntervals [||])))
            yield regexCase <|
                And (Star (Or (Concat (Epsilon, Epsilon), Negate (Epsilon))), And (And (Epsilon, Epsilon), And (Epsilon, Epsilon)))
            yield regexCase <|
                And (Star (CharacterSet CharSet.Empty), And (And (Epsilon, Epsilon), And (Epsilon, Epsilon)))
            yield regexCase <|
                Or (Or (Epsilon, CharacterSet CharSet.Empty), Epsilon)
            yield regexCase <|
                Or (
                    Or (Epsilon,
                        CharacterSet (CharSet.OfIntervals [| '\u001c', '\u001c'; '\u003c', '\u003c'; '\u005c', '\u005c' |])),
                    CharacterSet (CharSet.OfIntervals [| '\u0008', '\u0008'; '\u000a', '\u000a'; '\u0015', '\u0015'; '\u0020', '\u0020';  '\u0049', '\u0049'; '\u004b', '\u004b'; '\u0070', '\u0070' |]))
            yield regexCase <|
                And (
                    Star (CharacterSet (CharSet.OfArray [| '\u0017'; '\u0029'; '\u002c'; '\u0030'; '\u003c'; '\u0048'; '\u0066'; '\u0068' |])),
                    Star (CharacterSet (CharSet.OfArray [| '\u001c'; '\u0061'; '\u007a'; |])))
            }

        /// Gets a sequence of TestCaseData instances representing test cases for Regex.Simplify().
        member this.Items () =
            this.RawItems ()
            |> Seq.mapi (fun idx testCase ->
                RegexSimplifyTestCase.ToTestCaseData (idx, testCase))

    [<Test(Description = "Test cases for checking whether Regex.Simplify fully simplifies a Regex in one pass.")>]
    [<TestCaseSource(typeof<RegexSimplifyTestCases>, "Items")>]
    let ``Regex.Simplify is normalizing`` (inputRegex : Regex) : unit =
        // The regex should be fully simplified in one pass.
        let simplifiedRegex = Regex.Simplify inputRegex

        // Try to simplify the regex again.
        let doubleSimplifiedRegex = Regex.Simplify simplifiedRegex

        // Check whether the double-simplified regex is the same as the simplified regex.
        assertEqual doubleSimplifiedRegex simplifiedRegex


/// Randomized tests for the Regex type and module.
[<TestFixture>]
module RegexRandomizedTests =
    open System
    open System.IO

    /// Indicates whether or not test journaling is enabled.
    let [<Literal>] private testJournalingEnabled = true

    /// When test journaling is enabled, contains the filename to the journal file.
    let private testJournalFile =
        if testJournalingEnabled then
            // TODO : Write the journal to a folder within the facio tree instead (make the folder's excluded by the .gitignore).
            let desktop = Environment.GetFolderPath Environment.SpecialFolder.DesktopDirectory
            Some <| Path.Combine (desktop, "Reggie.Tests.RegexRandomized.Journal.txt")
        else None

    // These tests can sometimes find inputs that cause Regex.Simplify to crash with a StackOverflowException.
    // StackOverflowExceptions can't be caught, so the simplest way to discover the input that caused the crash
    // is to record each input to a file. If the test does not crash, the file is deleted afterward; otherwise,
    // the file will be left in place on the desktop and will contain the test case causing the crash.
    let private assertRegexProp testName predicate =
        FsCheckJournaled.assertProp testJournalFile testName (fun tw regex -> Regex.PrintFSharpCode(regex, tw)) predicate

    let private assertRegexPropN testName maxTest predicate =
        FsCheckJournaled.assertPropN testJournalFile testName maxTest (fun tw regex -> Regex.PrintFSharpCode(regex, tw)) predicate

    [<Test(Description = "Checks that the PrintFSharpCode method always succeeds.")>]
    let ``PrintFSharpCode always succeeds`` () : unit =
        // Re-use a StringWriter here to speed up the test by avoiding the allocations from
        // re-creating it for each Regex (and from allocating the string containing the code).
        using (new StringWriter ()) <| fun sw ->
        assertProp "PrintFSharpCode always succeeds" <| fun regex ->
            // Try to run PrintFSharpCode against any Regex. If it doesn't raise an exception,
            // consider the operation to have succeeded.
            try
                Regex.PrintFSharpCode (regex, sw)
                true
            with ex ->
                stderr.WriteLine ex
                false

    [<Test(Description = "Checks that the 'simplify' operation is strongly normalizing; \
        i.e., once a regex is simplified, it can't be simplified further.")>]
    let ``simplify operation is normalizing`` () : unit =
        assertRegexPropN "simplify is strongly normalizing" 20000 <| fun regex ->
            // Simplify the regex.
            let simplifiedRegex = Regex.Simplify regex

            // Try to simplify the regex again.
            let doubleSimplifiedRegex = Regex.Simplify simplifiedRegex

            // Check whether the double-simplified regex is the same as the simplified regex.
            simplifiedRegex = doubleSimplifiedRegex

    [<Test>]
    [<Ignore("This test is a prototype and still needs to be verified against the implementation.")>]
    let ``difference of a language and itself is the null language`` () =
        assertRegexProp "difference of a language and itself is the null language" <| fun regex ->
            // Calculate the difference of the regex and itself.
            let diff = Regex.Difference (regex, regex)

            // The difference should be the null language.
            diff = Regex.Epsilon

    [<Test>]
    [<Ignore("This test is a prototype and still needs to be verified against the implementation.")>]
    let ``a language AND-ed with itself then simplified returns the original language`` () =
        assertRegexProp "a language AND-ed with itself then simplified returns the original language" <| fun regex ->
            // AND the langugage with itself, then simplify.
            let result = Regex.andr regex regex

            // Simplify the original regex.
            let simplifiedRegex = Regex.Simplify regex

            // The regex and'ed with itself and simplified should equal the simplified regex.
            simplifiedRegex = result

    [<Test>]
    [<Ignore("This test is a prototype and still needs to be verified against the implementation.")>]
    let ``a language OR-ed with itself then simplified returns the original language`` () =
        assertRegexProp "a language OR-ed with itself then simplified returns the original language" <| fun regex ->
            // OR the langugage with itself, then simplify.
            let result = Regex.orr regex regex

            // Simplify the original regex.
            let simplifiedRegex = Regex.Simplify regex

            // The regex or'ed with itself and simplified should equal the simplified regex.
            simplifiedRegex = result
