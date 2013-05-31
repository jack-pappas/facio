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

namespace Tests.FSharpYacc

open System.Diagnostics
open System.IO
open NUnit.Framework
open FsUnit


/// Helper functions and values for implementing file-based test cases.
[<AutoOpen>]
module private TestCaseHelpers =
    //
    let private startOverlap (str1 : string) (str2 : string) : string =
        notImpl "TestCaseHelpers.startOverlap"

    /// The absolute path to the fsharpyacc executable to test.
    let toolPath =
        notImpl "TestCaseHelpers.toolPath"
        ""

    //
    let repositoryRoot =
        notImpl "TestCaseHelpers.repositoryRoot"
        ""

    //
    let testCases () =
        // TODO : Implement this so it searches the TestCases directory and
        // it's children instead of hard-coding the return values.
        seq {
            yield TestCaseData (
                [| box @"C:\Users\Jack\Documents\Code Libraries\fsharp-tools\TestCases\fslex.fsy";          // Input (specification)
                   box @"C:\Users\Jack\Documents\Code Libraries\fsharp-tools\TestCases\fslex-parser.fs";    // Output (F# source)
                   box true;                                                                                // Generate an internal module?
                   box "Parser";                                                                            // The name of the generated module.
                   |])
            yield TestCaseData (
                [| box @"C:\Users\Jack\Documents\Code Libraries\fsharp-tools\TestCases\fsyacc.fsy";          // Input (specification)
                   box @"C:\Users\Jack\Documents\Code Libraries\fsharp-tools\TestCases\fsyacc-parser.fs";    // Output (F# source)
                   box true;                                                                                 // Generate an internal module?
                   box "Parser";                                                                             // The name of the generated module.
                   |])
            }


//
type RepositoryTestCases () =
    //
    member __.Items
        with get () =
            testCases () :> System.Collections.IEnumerable


/// Run fsharpyacc against the test cases in the repository.
[<TestFixture>]
module TestCases =
    open System
    open System.Threading

    //
    let private testTimeout = TimeSpan.FromSeconds 60.0

    //
    [<TestCaseSource(typeof<RepositoryTestCases>, "Items")>]
    let repository (inputFilename : string, outputFilename : string, internalModule : bool, parserModuleName : string) =
        //
        use toolProcess = new Process ()
        
        // Set the process' start info.
        toolProcess.StartInfo <-
            //
            let toolProcessStartInfo =
                let processArgs =
                    let internalModule = if internalModule then "--internal " else ""
                    sprintf "%s--module \"%s\" -o \"%s\" \"%s\""
                        internalModule parserModuleName outputFilename inputFilename
            
                ProcessStartInfo (toolPath, processArgs)

            // Set additional properties of the ProcessStartInfo.
            toolProcessStartInfo.CreateNoWindow <- true
            toolProcessStartInfo

        (* TODO : Add additional code to capture output and error information
                  from the process, then log it through NUnit. *)

        // Start the process.
        if not <| toolProcess.Start () then
            Assert.Fail "Unable to start the external tool process."

        // Wait for the process to complete.
        while not toolProcess.HasExited && DateTime.Now - toolProcess.StartTime < testTimeout do
            Thread.Sleep (TimeSpan.FromSeconds 5.0)

        // If the process has not completed yet, it's considered to be "timed out" so kill it.
        if not toolProcess.HasExited then
            toolProcess.Kill ()
            Assert.Inconclusive "The external tool process timed out."
        else
            // Based on the process' exit code, assert that the test passed or failed.
            if toolProcess.ExitCode = 0 then
                // TODO : Provide a message with timing information.
                Assert.Pass ()
            else
                let msg = sprintf "THe external tool process exited with code %i." toolProcess.ExitCode
                Assert.Fail msg
