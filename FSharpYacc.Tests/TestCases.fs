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
    open System.Runtime.InteropServices
    open System.Threading
    

    [<Flags>]
    type ErrorModes =
        | SYSTEM_DEFAULT             = 0x00000000u
        | SEM_FAILCRITICALERRORS     = 0x00000001u
        | SEM_NOGPFAULTERRORBOX      = 0x00000002u
        | SEM_NOALIGNMENTFAULTEXCEPT = 0x00000004u
        | SEM_NOOPENFILEERRORBOX     = 0x00008000u

    [<DllImport("kernel32.dll")>]
    extern ErrorModes public SetErrorMode (ErrorModes uMode)

    [<TestFixtureSetUp>]
    let textFixtureSetup () : unit =
        // When running on Windows (even if running on Mono), disable crash-reporting dialog.
        match System.Environment.OSVersion.Platform with
        | PlatformID.Win32NT
        | PlatformID.Win32S
        | PlatformID.Win32Windows
        | PlatformID.WinCE ->
            // Disable the crash dialog. This affects not only this process,
            // but also any child processes (which is really what we care about).
            let oldMode = SetErrorMode ErrorModes.SEM_NOGPFAULTERRORBOX
            SetErrorMode (oldMode ||| ErrorModes.SEM_NOGPFAULTERRORBOX) |> ignore
        | _ ->
            // For all other platforms, this is a no-op.
            ()

    //
    let private testTimeout = TimeSpan.FromSeconds 30.0

    //
    type private RepositoryTestCases () =
        //
        member __.Items
            with get () =
                testCases () :> System.Collections.IEnumerable

    //
    [<Test; TestCaseSource(typeof<RepositoryTestCases>, "Items")>]
    let repository (inputFilename : string, outputFilename : string, internalModule : bool, parserModuleName : string) =
        // Test cases may be ignored by adding a text file with the same filename as the input file, plus the suffix ".ignore".
        if File.Exists (inputFilename + ".ignore") then
            let ignoreMsg = sprintf "Ignoring test case '%s'." inputFilename
            Assert.Ignore ignoreMsg
    
        let sw = System.Diagnostics.Stopwatch.StartNew()
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
            toolProcessStartInfo.ErrorDialog <- false
            toolProcessStartInfo.WindowStyle <- ProcessWindowStyle.Hidden
            toolProcessStartInfo.WorkingDirectory <- Path.GetDirectoryName toolPath
            toolProcessStartInfo.UseShellExecute <- false
            toolProcessStartInfo.RedirectStandardError <- true
            toolProcessStartInfo.RedirectStandardOutput <- true
            toolProcessStartInfo

        // Start the process.
        if not <| toolProcess.Start () then
            Assert.Fail "Unable to start the external tool process."

        // Wait for the process to complete.
        if not <| toolProcess.WaitForExit (int testTimeout.TotalMilliseconds) then
            // If the process has not completed yet, it's considered to be "timed out" so kill it.
            toolProcess.Kill ()
            Assert.Inconclusive "The external tool process timed out."
        else
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
            if toolProcess.ExitCode = 0 then
                Assert.Pass (sprintf "The execution took %A for file %s" sw.Elapsed inputFilename)
            else
                let msg = sprintf "The external tool process exited with code %i.\n%s" toolProcess.ExitCode (details.ToString())
                Assert.Fail msg
