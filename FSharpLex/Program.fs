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

//
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
    [<assembly: DependencyAttribute("FSharp.Core", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System.ComponentModel.Composition", LoadHint.Always)>]

    // Appease the F# compiler
    do ()


//
[<RequireQualifiedAccess>]
module Program =
    open System.ComponentModel.Composition
    open System.ComponentModel.Composition.Hosting
    open ExtCore.Args
    open FSharpLex.Plugin

    (* TEMP : This code is taken from the F# Powerpack, and is licensed under the Apache 2.0 license *)
    open System.IO
    open Microsoft.FSharp.Text.Lexing
    //------------------------------------------------------------------
    // This code is duplicated from Microsoft.FSharp.Compiler.UnicodeLexing

    type private Lexbuf =  LexBuffer<char>

    /// Standard utility to create a Unicode LexBuffer
    ///
    /// One small annoyance is that LexBuffers and not IDisposable. This means
    /// we can't just return the LexBuffer object, since the file it wraps wouldn't
    /// get closed when we're finished with the LexBuffer. Hence we return the stream,
    /// the reader and the LexBuffer. The caller should dispose the first two when done.
    let private UnicodeFileAsLexbuf (filename, codePage : int option) : FileStream * StreamReader * Lexbuf =
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
    (* End-TEMP *)

    //
    let private loadBackends () =
        //
        use catalog = new AssemblyCatalog (typeof<Backends>.Assembly)

        //
        use container = new CompositionContainer (catalog)

        //
        let backends = Backends ()
        container.ComposeParts (backends)
        backends

    let logger = NLog.LogManager.GetCurrentClassLogger()
    let loginfo (msg:string) = logger.Info msg
    let logexn msg exn = logger.ErrorException(msg, exn)
    let logerror (msg:string) = logger.Error msg

    //
    let private statusMessage msg (generator : unit -> 'T) : 'T =
        
        loginfo <| sprintf "%s..." msg
        let result = generator ()

        loginfo <| sprintf "done."
        result

    open FSharpLex.SpecializedCollections

    /// Invokes FSharpLex with the specified options.
    [<CompiledName("Invoke")>]
    let invoke (inputFile, options) : int =
        // Preconditions
        if inputFile = null then
            nullArg "inputFile"
        elif System.String.IsNullOrWhiteSpace inputFile then
            invalidArg "inputFile" "The path to the lexer specification is empty."
        elif not <| System.IO.File.Exists inputFile then
            invalidArg "inputFile" "No lexer specification exists at the specified path."

        // TEMP : This is hard-coded for now, but eventually we'll make it
        // so the user can specify which backend(s) to use.
        /// Compiler backends.
        let backends = statusMessage "Loading backends" loadBackends

        /// The parsed lexer specification.
        let lexerSpec =
            statusMessage "Parsing lexer specification" <| fun () ->
            
            let stream, reader, lexbuf =
                UnicodeFileAsLexbuf (inputFile, options.InputCodePage)
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
            with exn ->
                let pos = lexbuf.StartPos
                failwithf "could not parse the lexer spec: syntax error near line %d, column %d\n%s" pos.Line pos.Column exn.Message

        // Compile the parsed specification.
        let compiledSpecification =
            statusMessage "Compiling specification" <| fun () ->
                Compile.Compiler.lexerSpec lexerSpec options

        //
        match compiledSpecification with
        | Choice2Of2 errorMessages ->
            // Write the error messages to the console.
            // TODO : Write the error messages to NLog (or similar) instead, for flexibility.
            errorMessages
            |> Array.iter logerror

            1   // Exit code: Error

        | Choice1Of2 compiledLexerSpec ->
            statusMessage "Invoking backend to generate code" <| fun () ->
                // TEMP : Invoke the various backends "manually".
                // Eventually we'll modify this so the user can specify the backend to use.
                backends.FslexBackend.EmitCompiledSpecification (
                    compiledLexerSpec,
                    options)

    //            backends.GraphBackend.EmitCompiledSpecification (
    //                compiledLexerSpec,
    //                options)

            0   // Exit code: Success

    //
    let [<Literal>] defaultLexerInterpreterNamespace = "Microsoft.FSharp.Text.Lexing"
    
    // Variables to hold parsed command-line arguments.
    let inputFile = ref None
    let inputCodePage = ref None
    let outputFile = ref None
    let unicode = ref false
    let lexlib = ref defaultLexerInterpreterNamespace

    /// The entry point for the application.
    [<EntryPoint; CompiledName("Main")>]
    let main _ =
        try 
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
                    failwith "Error: Only one lexer specification file may be used as input."

            // Parse the command-line arguments.
            ArgParser.Parse (usage, plainArgParser, "fsharplex <filename>")

            // Validate the parsed arguments.
            // TODO

            // If the output file is not specified, use a default value.
            if Option.isNone !outputFile then
                outputFile := Some <| System.IO.Path.ChangeExtension (Option.get !inputFile, "fs")

            // Create a CompilationOptions record from the parsed arguments
            // and call the 'invoke' function with it.
            invoke (Option.get !inputFile, {
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
                })

        with exn ->
            logexn "Unrecoverable error" exn
            1