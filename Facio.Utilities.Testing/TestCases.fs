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

namespace Facio.Utilities.Testing

open System.Diagnostics
open System.IO
open NUnit.Framework


//
[<RequireQualifiedAccess>]
module TestSystem =
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

    /// Disables the crash-reporting dialog when running tests on Windows,
    /// since it interferes with automatically running test processes.
    [<CompiledName("DisableCrashReporting")>]
    let disableCrashReporting () : unit =
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
    [<CompiledName("CreateToolProcess")>]
    let createToolProcess toolPath processArgs workingDirectory =
        // Preconditions
        // TODO

        //
        let toolProcess = new Process ()
        
        // Set the process' start info and other properties.
        toolProcess.StartInfo <-
            //
            let toolProcessStartInfo = ProcessStartInfo (toolPath, processArgs)

            // Set additional properties of the ProcessStartInfo.
            toolProcessStartInfo.CreateNoWindow <- true
            toolProcessStartInfo.ErrorDialog <- false
            toolProcessStartInfo.RedirectStandardError <- true
            toolProcessStartInfo.RedirectStandardOutput <- true
            toolProcessStartInfo.UseShellExecute <- false
            toolProcessStartInfo.WindowStyle <- ProcessWindowStyle.Hidden

            // If no working directory is specified, start in the same directory as the tool we're going to run.
            toolProcessStartInfo.WorkingDirectory <-
                match workingDirectory with
                | None ->
                    Path.GetDirectoryName toolPath
                | Some workingDirectory ->
                    workingDirectory
            
            toolProcessStartInfo

        // Return the Process without starting it.
        toolProcess


/// Helper functions and values for implementing file-based test cases.
module Path =
    //
    let rec private findRepoRoot (path : string) =
        // Get the directory containing the path.
        let dirPath = Path.GetDirectoryName path

        // Does this directory contain a directory called ".git"?
        if Directory.Exists <| Path.Combine (dirPath, ".git") then
            dirPath
        elif Path.GetPathRoot path = dirPath then
            // We've reach the root of a drive, so raise an exception.
            raise <| exn "Unable to locate the root folder of the repository."
        else
            // Continue recursing upwards
            findRepoRoot dirPath

    type private Dummy () = class end

    //
    [<CompiledName("RepositoryRoot")>]
    let repositoryRoot =
        (System.Uri (typeof<Dummy>.Assembly.CodeBase)).LocalPath
        |> findRepoRoot
