(*

Copyright 2013 Jack Pappas

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

/// Run fsharpyacc against the test cases in the repository.
[<NUnit.Framework.TestFixture>]
module Tests.FSharpYacc.TestCases

open System
open System.Diagnostics
open System.IO
open System.Threading
open NUnit.Framework
open Facio.Utilities.Testing


[<TestFixtureSetUp>]
let textFixtureSetup () : unit =
    // When running on Windows (even if running on Mono), disable crash-reporting dialog.
    TestSystem.disableCrashReporting ()

//
let private testTimeout = TimeSpan.FromSeconds 30.0

/// The absolute path to the fsharpyacc executable to test.
let private toolPath =
    (System.Uri (typeof<FSharpYacc.FsyaccBackendOptions>.Assembly.CodeBase)).LocalPath

//
type private RepositoryTestCases () =
    //
    member __.Items
        with get () =
            Directory.EnumerateFiles (
                Path.Combine (Path.repositoryRoot + Path.DirectorySeparatorChar.ToString (), "TestCases"),
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
            :> System.Collections.IEnumerable

//
[<Test; TestCaseSource(typeof<RepositoryTestCases>, "Items")>]
let repository (inputFilename : string, outputFilename : string, internalModule : bool, parserModuleName : string) =
    // Test cases may be ignored by adding a text file with the same filename as the input file, plus the suffix ".ignore".
    if File.Exists (inputFilename + ".ignore") then
        let ignoreMsg = sprintf "Ignoring test case '%s'." inputFilename
        Assert.Ignore ignoreMsg

    let shouldFail = File.Exists (inputFilename + ".shouldfail")

    //
    use toolProcess =
        let processArgs =
            sprintf "%s--module \"%s\" -o \"%s\" \"%s\""
                (if internalModule then "--internal " else "")
                parserModuleName
                outputFilename
                inputFilename

        TestSystem.createToolProcess toolPath processArgs None

    // Start the process.
    if not <| toolProcess.Start () then
        Assert.Fail "Unable to start the external tool process."

    // Wait for the process to complete.
    if not <| toolProcess.WaitForExit (int testTimeout.TotalMilliseconds) then
        // If the process has not completed yet, it's considered to be "timed out" so kill it.
        toolProcess.Kill ()
        Assert.Inconclusive "The external tool process timed out."
    
    // Read the error/output streams from the process, then write them into the
    // error/output streams of this process so they can be captured by NUnit.
    let details = System.Text.StringBuilder()
    do
        let errorStr = toolProcess.StandardError.ReadToEnd ()
        if not <| String.IsNullOrWhiteSpace errorStr then
            System.Console.Error.Write errorStr
            Printf.bprintf details "Errors: %s" errorStr

    do
        let outputStr = toolProcess.StandardOutput.ReadToEnd ()
        if not <| String.IsNullOrWhiteSpace outputStr then
            System.Console.Out.Write outputStr
            Printf.bprintf details "Console output: %s" outputStr

    // Based on the process' exit code, assert that the test passed or failed.
    if (toolProcess.ExitCode <> 0) = shouldFail then
        let elapsedTime = toolProcess.ExitTime - toolProcess.StartTime
        let msg = sprintf "The execution took %A for file %s" elapsedTime inputFilename
        Assert.Pass msg
    else
        let msg =
            if shouldFail then
                sprintf "The test case %s should have failed, but in fact ran successfully." inputFilename
            else
                sprintf "The external tool process exited with code %i.%s%O" toolProcess.ExitCode Environment.NewLine details

        Assert.Fail msg
