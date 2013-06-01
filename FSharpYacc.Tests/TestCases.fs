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
    let rec private findRepoRoot (path : string) =
        // Get the directory containing the path.
        let dirPath = Path.GetDirectoryName path

        // Does this directory contain a directory called ".git"?
        if Directory.Exists <| Path.Combine (dirPath, ".git") then
            dirPath
        elif Path.GetPathRoot path = dirPath then
            // We've reach the root of a drive, so raise an exception.
            failwith "Unable to locate the root folder of the repository."
        else
            // Continue recursing upwards
            findRepoRoot dirPath
        
    /// The absolute path to the fsharpyacc executable to test.
    let toolPath =
        (System.Uri (typeof<FSharpYacc.FsyaccBackendOptions>.Assembly.CodeBase)).LocalPath

    type private Dummy () = class end

    //
    let repositoryRoot =
        (System.Uri (typeof<Dummy>.Assembly.CodeBase)).LocalPath
        |> findRepoRoot

    //
    let testCases () =
        Directory.EnumerateFiles (
            Path.Combine (repositoryRoot + Path.DirectorySeparatorChar.ToString (), "TestCases"),
            "*.fsy",
            SearchOption.AllDirectories)
        |> Seq.map (fun testCaseFile ->
            /// The output file name, which is based on the input filename.
            let outputFile =
                Path.Combine (
                    Path.GetDirectoryName testCaseFile,
                    Path.GetFileNameWithoutExtension testCaseFile + "-parser.fs")

            TestCaseData (
                [| box testCaseFile;    // Input (specification)
                   box outputFile;      // Output (F# source)
                   box true;            // Generate an internal module?
                   box "Parser";        // The name of the generated module.
                   |]))


/// Run fsharpyacc against the test cases in the repository.
[<TestFixture>]
module TestCases =
    open System
    open System.Threading

    //
    let private testTimeout = TimeSpan.FromSeconds 60.0

    //
    type private RepositoryTestCases () =
        //
        member __.Items
            with get () =
                testCases () :> System.Collections.IEnumerable

    //
    [<TestCaseSource(typeof<RepositoryTestCases>, "Items")>]
    let repository (inputFilename : string, outputFilename : string, internalModule : bool, parserModuleName : string) =
        //
        use toolProcess = new Process ()
        
        // Set the process' start info and other properties.
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
            toolProcessStartInfo.WorkingDirectory <- Path.GetDirectoryName toolPath
            toolProcessStartInfo.UseShellExecute <- true
            toolProcessStartInfo

        (* TODO : Add additional code to capture output and error information
                  from the process, then log it through NUnit. *)

        // Start the process.
        if not <| toolProcess.Start () then
            Assert.Fail "Unable to start the external tool process."

        // Wait for the process to complete.
        while not toolProcess.HasExited && DateTime.Now - toolProcess.StartTime < testTimeout do
            Thread.Sleep (TimeSpan.FromSeconds 1.0)

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
                let msg = sprintf "The external tool process exited with code %i." toolProcess.ExitCode
                Assert.Fail msg
