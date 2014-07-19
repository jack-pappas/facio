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

(**************************************
MSBuild task for fsharpyacc

fsharpyacc <filename>
        -o <string>: The path where the output file will be written.
        -v: Produce a listing file.
        --module <string>: The name to use for the F# module containing the generated parser. The default is 'Parser'.
        --internal: Generate an internal module
        --open <string>: Add the given module to the list of those to open in both the generated signature and implementation.
        --lexlib <string>: Specify the namespace for the implementation of the lexer table interpreter. The default is 'Microsoft.FSharp.Text.Lexing'.
        --parslib <string>: Specify the namespace for the implementation of the parser table interpreter. The default is 'Microsoft.FSharp.Text.Parsing'.
        --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
        --help: display this list of options
        -help: display this list of options
**************************************)

/// MSBuild task for invoking fsharpyacc.
[<Sealed>]
type FSharpYaccTask () = 
    inherit Task ()

    // Install the assembly-resolution handler before doing anything else,
    // to ensure we don't crash because the CLR can't find certain assemblies.
    do
        let resolutionHelper = ResolveHelper ()
        resolutionHelper.InstallHandler ()
    
    //
    [<Required>]
    member val InputFile = null : string with get, set
    
    //
    [<Output>]
    member val OutputFile = null : string with get, set
    
    // --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
    member val CodePage = null : string with get, set

    // --lexlib: Specify the namespace where the lexer table interpreter can be found.
    member val LexerInterpreterNamespace = null : string with get, set

    // --parslib: Specify the namespace where the parser table interpreter can be found.
    member val ParserInterpreterNamespace = null : string with get, set

    // --open: Specify additional namespaces/modules to be opened by the generated module.
    member val OpenNamespaces = [| |] : string[] with get, set

    // --module: The full name to use for the generated parser module.
    member val ModuleName = null : string with get, set

    // -v: Produce a listing file.
    member val EmitListingFile = false with get, set

    // --internal: Generate an internal module
    member val Internal = false with get, set

    override this.Execute () =
        // Configure NLog to use our MSBuild-style target.
        Config.SimpleConfigurator.ConfigureForTargetLogging (new MSBuildLogTarget(this.Log, this.InputFile))

        /// The NLog logger.
        let logger = NLog.LogManager.GetCurrentClassLogger ()

        // TEMP : fsharpyacc does not yet support the '-v' option, so emit a warning message if that property is set.
        if this.EmitListingFile then
            logger.Warn "fsharpyacc does not yet support the '-v' option to emit listing files, so this flag will be ignored."

        //
        let outputFile =
            // If the output file is not specified, use a default value.
            match this.OutputFile with
            | null ->
                System.IO.Path.ChangeExtension (this.InputFile, "fs")
            | outputFile ->
                outputFile

        let inputCodePage =
            match Int32.TryParse this.CodePage with
            | true, codePage -> Some codePage
            | _ -> None

        let compilationOptions : FSharpYacc.CompilationOptions = {
            ParserType = FSharpYacc.ParserType.Lalr1;
            FsyaccBackendOptions = Some {
                OutputPath = outputFile;
                ModuleName =
                    match this.ModuleName with null -> None | x -> Some x;
                LexerInterpreterNamespace =
                    match this.LexerInterpreterNamespace with null -> None | x -> Some x;
                ParserInterpreterNamespace =
                    match this.ParserInterpreterNamespace with null -> None | x -> Some x;
                OpenDeclarations = this.OpenNamespaces;
                InternalModule = this.Internal;
                // TODO : Support the '-v' (this.EmitListingFile) option.
                };
            }

        logger.Trace "Invoking fsharpyacc..."

        try
            FSharpYacc.Program.invoke this.InputFile compilationOptions inputCodePage logger = 0
        with ex ->
            // Log any unhandled exceptions raised by fsharpyacc.
            logger.FatalException ("Unhandled exception raised by fsharpyacc.", ex)
            false
        