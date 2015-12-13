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

namespace FSharpLex

open System.ComponentModel.Composition
open Reggie.Plugin
open FSharpLex.Plugin


/// Assembly info for FSharpLex.
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

    (* Dependency hints for Ngen *)
    [<assembly: DependencyAttribute("Reggie", LoadHint.Always)>]
    [<assembly: DependencyAttribute("ExtCore", LoadHint.Always)>]
    [<assembly: DependencyAttribute("FSharp.Core", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System.ComponentModel.Composition", LoadHint.Always)>]

    // Appease the F# compiler
    do ()


/// Contains functions for working with fslexyacc lex buffers.
[<RequireQualifiedAccess>]
module private FsLexYaccBuffer =
    (* TEMP : This code is taken from the F# Powerpack, and is licensed under the Apache 2.0 license *)
    open System.IO
    open Microsoft.FSharp.Text.Lexing
    //------------------------------------------------------------------
    // This code is duplicated from Microsoft.FSharp.Compiler.UnicodeLexing

    /// Standard utility to create a Unicode LexBuffer
    ///
    /// One small annoyance is that LexBuffers are not IDisposable. This means
    /// we can't just return the LexBuffer object, since the file it wraps wouldn't
    /// get closed when we're finished with the LexBuffer. Hence we return the stream,
    /// the reader and the LexBuffer. The caller should dispose the first two when done.
    let UnicodeFileAsLexbuf (filename, codePage : int option) : FileStream * StreamReader * LexBuffer<char> =
        // Use the .NET functionality to auto-detect the unicode encoding
        // It also uses Lexing.from_text_reader to present the bytes read to the lexer in UTF8 decoded form
        let stream = new FileStream (filename, FileMode.Open, FileAccess.Read, FileShare.Read)
        let reader =
            match codePage with
            | None ->
                new StreamReader (stream, true)
            | Some n ->
                new StreamReader (stream, System.Text.Encoding.GetEncoding n)
        let lexbuf = LexBuffer.FromFunction reader.Read
        lexbuf.EndPos <- Position.FirstLine filename
        stream, reader, lexbuf


/// FSharpLex program exit codes.
type ExitCode =
    /// The program completed successfully.
    | Success = 0
    /// The program encountered an unrecoverable error.
    | UnrecoverableError = 1


/// FSharpLex compiler instance.
type FSharpLex (logger : NLog.Logger) =
    // Remove the global trace lock. It's not needed and impacts
    // performance when running with tracing enabled.
    static do
        System.Diagnostics.Trace.UseGlobalLock <- false

    /// Backends to invoke with the compiled specification.
    [<ImportMany>]
    member val Backends : IBackend[] = null with get, set

    /// <summary>Try to parse a lexer specification from a specification file.</summary>
    /// <param name="inputFile"></param>
    /// <param name="inputCodePage"></param>
    /// <returns></returns>
    member internal __.TryParseLexerSpecFile (inputFile : string, inputCodePage : int option) : _ option =
        let stream, reader, lexbuf =
            FsLexYaccBuffer.UnicodeFileAsLexbuf (inputFile, inputCodePage)
        use stream = stream
        use reader = reader
        try
            let lexerSpec = Parser.spec Lexer.token lexbuf

            // TEMP : Some of the lists need to be reversed so they're in the order we expect.
            { lexerSpec with
                Macros = List.rev lexerSpec.Macros;
                Rules =
                    lexerSpec.Rules
                    |> List.map (fun (position, rule) ->
                        position,
                        { rule with
                            Parameters = List.rev rule.Parameters;
                            Clauses = List.rev rule.Clauses; })
                    |> List.rev; }
            |> Some

        with ex ->
            let msg =
                let pos = lexbuf.StartPos
                sprintf "Could not parse the lexer spec: syntax error near line %d, column %d" pos.Line pos.Column
            logger.FatalException (msg, ex)

            // Return None since the spec file couldn't be parsed.
            None

    /// Invokes FSharpLex with the specified options.
    member this.Run (inputFile, options : Reggie.CompilationOptions) : ExitCode =
        // Contracts
        checkNonNull "inputFile" inputFile
        if System.String.IsNullOrWhiteSpace inputFile then
            invalidArg "inputFile" "The path to the lexer specification is empty."
        elif not <| System.IO.File.Exists inputFile then
            invalidArg "inputFile" "No lexer specification exists at the specified path."

        // Try to parse the lexer specification.
        match this.TryParseLexerSpecFile (inputFile, options.InputCodePage) with
        | None ->
            // Couldn't parse the lexer spec, so exit with an error code.
            ExitCode.UnrecoverableError

        | Some lexerSpec ->
            // Compile the parsed specification.
            let compiledSpecification =
                logger.Trace "Start: Compiling lexer specification."
                Reggie.Compile.Compiler.lexerSpec lexerSpec options
            logger.Trace "End: Compiling lexer specification."

            // Check whether the specification was compiled successfully or not.
            match compiledSpecification with
            | Choice2Of2 errorMessages ->
                // Write the error messages to the console.
                errorMessages
                |> Array.iter logger.Error

                ExitCode.UnrecoverableError

            | Choice1Of2 compiledLexerSpec ->
                // If there aren't any backends available, log a warning message and return.
                match this.Backends with
                | null ->
                    logger.Warn "No compiler backends selected."
                    ExitCode.Success

                | backends ->
                    // Emit the number of backends for tracing purposes.
                    logger.Trace ("{0} compiler backends to invoke.", backends.Length)

                    // Iterate over the backends, invoking each one with the compiled lexer spec
                    // and the specified compiler options.
                    // TODO : It'd be nice to be able to pass each backend it's own specific set of options
                    //        rather than having to pass one huge record holding all of the options.
                    // TODO : Modify IBackend.EmitCompiledSpecification() so it allows the backends to indicate
                    //        when they've failed (e.g., by returning Protected<unit>). For additional safety,
                    //        also modify the loop below to wrap the backend invocations in a try/with (or Choice.attempt)
                    //        in case a backend doesn't catch some exception. If one or more backends fails,
                    //        we still want to attempt to run the rest of the backends but we'll also want to return
                    //        an ExitCode indicating failure.
                    for backend in backends do
                        let backendName = backend.Name
                        logger.Trace ("Start: Invoking backend '{0}'.", backendName)
                        backend.EmitCompiledSpecification (compiledLexerSpec, options)
                        logger.Trace ("End: Invoking backend '{0}'.", backendName)

                    ExitCode.Success


/// FSharpLex "driver" program.
/// This is used to invoke the FSharpLex compiler via the command-line.
[<RequireQualifiedAccess>]
module Program =
    open System.ComponentModel.Composition.Hosting
    open ExtCore.Args
    open Reggie

    //
    let [<Literal>] defaultLexerInterpreterNamespace = "Microsoft.FSharp.Text.Lexing"

    /// The entry point for the application.
    [<EntryPoint; CompiledName("Main")>]
    let main _ =
        /// Used for writing messages to the console or log file.
        let logger = NLog.LogManager.GetCurrentClassLogger ()

        // Variables to hold parsed command-line arguments.
        let inputFile = ref None
        let inputCodePage = ref None
        let outputFile = ref None
        let unicode = ref false
        let lexlib = ref defaultLexerInterpreterNamespace

        /// Command-line options.
        let usage =
            [|  ArgInfo.Create ("-o", ArgType.String (fun s -> outputFile := Some s),
                    "The path where the generated lexer source code will be written.");
                ArgInfo.Create ("--codepage", ArgType.Int (fun i -> inputCodePage := Some i),
                    "Assume input lexer specification file is encoded with the given codepage.");
                ArgInfo.Create ("--lexlib", ArgType.String (fun s -> lexlib := s),
                    sprintf "Specify the namespace for the implementation of the lexer table interpreter. \
                    The default is '%s'." defaultLexerInterpreterNamespace);
                ArgInfo.Create ("--unicode", ArgType.Set unicode,
                    "Produce a lexer which supports 16-bit Unicode characters."); |]

        // Parses argument values which aren't specified by flags.
        let plainArgParser x =
            match !inputFile with
            | None ->
                inputFile := Some x
            | Some _ ->
                // If the input filename has already been set, print a message
                // to the screen, then exit with an error code.
                logger.Error "Only one lexer specification file may be used as input."
                exit (int ExitCode.UnrecoverableError)

        // Parse the command-line arguments.
        ArgParser.Parse (usage, plainArgParser, "fsharplex <filename>")

        // Validate the parsed arguments.
        // TODO

        // If the output file is not specified, use a default value.
        if Option.isNone !outputFile then
            outputFile := Some <| System.IO.Path.ChangeExtension (Option.get !inputFile, "fs")

        // Create a CompilationOptions record from the parsed arguments.
        let compilationOptions = {
            Unicode = !unicode;
            InputCodePage = !inputCodePage;

            // TEMP : These should be specified in a better way -- perhaps we can get
            // ArgInfo instances from the plugins along with some object which holds ref values
            // internally (used by the returned ArgInfo instances), which has a method
            // that produces an instance of FslexBackendOptions or GraphBackendOptions.
            FslexBackendOptions = Some {
                OutputPath = Option.get !outputFile;
                LexerLibraryNamespace = !lexlib;
                };
            GraphBackendOptions = Some {
                OutputPath =
                    System.IO.Path.ChangeExtension (Option.get !outputFile, "dgml");
                Format = GraphFileFormat.Dgml; };
            }

        // Discover and instantiate compiler backends.
        // TODO : This currently instantiates all available backends. This code should be moved up
        // to run prior to creating 'compilationOptions', then should only instantiate the backends
        // selected via command-line options.
        use catalog = new AssemblyCatalog (typeof<FSharpLex>.Assembly)
        use container = new CompositionContainer (catalog)

        /// An instance of the FSharpLex compiler.
        let compiler = FSharpLex (logger)

        // Instantiate backends and inject them into the compiler instance.
        container.ComposeParts (compiler)

        // Run the compiler with the specified options and backends.
        int <| compiler.Run (Option.get !inputFile, compilationOptions)
