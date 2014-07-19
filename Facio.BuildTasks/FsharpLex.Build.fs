(*

Copyright 2005-2009 Microsoft Corporation
Copyright 2014 Jack Pappas

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

namespace Facio.BuildTasks

open System
open Microsoft.Build.Framework
open Microsoft.Build.Utilities
open NLog
open NLog.Targets

(**************************************
MSBuild task for fsharplex

fsharplex <filename>
        -o <string>: The path where the generated lexer source code will be written.
        --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
        --lexlib <string>: Specify the namespace for the implementation of the lexer table interpreter. The default is 'Microsoft.FSharp.Text.Lexing'.
        --unicode: Produce a lexer which supports 16-bit Unicode characters.
        --help: display this list of options
        -help: display this list of options
**************************************)

/// MSBuild task for invoking fsharplex.
[<Sealed>]
type FSharpLexTask () =
    inherit Task ()

    // Install the assembly-resolution handler before doing anything else,
    // to ensure we don't crash because the CLR can't find certain assemblies.
    do
        let resolutionHelper = ResolveHelper ()
        resolutionHelper.InstallHandler ()

    //do this.StandardOutputImportance <- "Normal"

    //
    [<Required>]
    member val InputFile = null : string with get, set
    
    //
    [<Output>]
    member val OutputFile = null : string with get, set
    
    // --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
    member val CodePage = null : string with get, set
    
    // --unicode: Produce a lexer for use with 16-bit unicode characters.
    member val Unicode = false with get, set

    // --lexlib: Specify the namespace where the lexer table interpreter can be found.
    member val LexerInterpreterNamespace = null : string with get, set
        
    override this.Execute() =
        // Configure NLog to use our MSBuild-style target.
        Config.SimpleConfigurator.ConfigureForTargetLogging (new MSBuildLogTarget(this.Log, this.InputFile))

        /// The output filename (for the fslex-compatible backend).
        let outputFile =
            // If the output file is not specified, use a default value.
            match this.OutputFile with
            | null ->
                System.IO.Path.ChangeExtension (this.InputFile, "fs")
            | outputFile ->
                outputFile

        let lexlib =
            match this.LexerInterpreterNamespace with
            | null -> FSharpLex.Program.defaultLexerInterpreterNamespace
            | lexlib -> lexlib

        let inputCodePage =
            match Int32.TryParse this.CodePage with
            | true, codePage -> Some codePage
            | _ -> None

        let options : FSharpLex.CompilationOptions = {
            Unicode = this.Unicode;
            InputCodePage = inputCodePage;
            FslexBackendOptions = Some {
                OutputPath = outputFile;
                LexerLibraryNamespace = lexlib;
                };
            GraphBackendOptions = None;
            }

        let logger = NLog.LogManager.GetCurrentClassLogger ()
        logger.Trace "Invoking fsharplex..."

        try
            FSharpLex.Program.invoke this.InputFile options logger = 0
        with ex ->
            // Log any unhandled exceptions raised by fsharplex.
            logger.FatalException ("Unhandled exception raised by fsharplex.", ex)
            false
