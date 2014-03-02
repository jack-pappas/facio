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

namespace FSharpYacc

/// Assembly-level attributes specific to this assembly.
module private AssemblyInfo =
    open System.Reflection
    open System.Resources
    open System.Runtime.CompilerServices
    open System.Runtime.InteropServices
    open System.Security
    open System.Security.Permissions

    [<assembly: AssemblyTitle("FSharpYacc")>]
    [<assembly: AssemblyDescription("A 'yacc'-inspired parser-generator tool for F#.")>]
    [<assembly: NeutralResourcesLanguage("en-US")>]
    [<assembly: Guid("fc309105-ce95-46d1-8cb4-568fc6bea85c")>]

    (*  Makes internal modules, types, and functions visible
        to the test project so they can be unit-tested. *)
    #if DEBUG
    [<assembly: InternalsVisibleTo("FSharpYacc.Tests")>]
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
    open NLog
    open ExtCore.Args
    open FSharpYacc.Plugin

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

    /// Invokes FSharpYacc with the specified options.
    [<CompiledName("Invoke")>]
    let invoke inputFile options inputCodePage : int =
        // Preconditions
        if inputFile = null then
            nullArg "inputFile"
        elif System.String.IsNullOrWhiteSpace inputFile then
            invalidArg "inputFile" "The path to the parser specification is empty."
        elif not <| System.IO.File.Exists inputFile then
            invalidArg "inputFile" "No parser specification exists at the specified path."

        /// Used for writing messages to the console or log file.
        let logger = LogManager.GetCurrentClassLogger ()

        // TEMP : This is hard-coded until we implement functionality to
        // allow the user to select which backend to use.
        let backends = loadBackends ()

        /// The parsed parser specification.
        let parserSpec =
            try
                let stream, reader, lexbuf =
                    UnicodeFileAsLexbuf (inputFile, inputCodePage)
                use stream = stream
                use reader = reader
                let parserSpec = Parser.spec Lexer.token lexbuf

                // TEMP : Need to do a little massaging of the Specification for now to put some lists in the correct order.
                { parserSpec with
                    TerminalDeclarations =
                        parserSpec.TerminalDeclarations
                        |> List.map (fun (declaredType, terminals) ->
                            declaredType, List.rev terminals);
                    Productions =
                        parserSpec.Productions
                        |> List.map (fun (nonterminal, rules) ->
                            nonterminal,
                            rules
                            |> List.map (fun rule ->
                                { rule with
                                    Symbols = List.rev rule.Symbols; })
                            |> List.rev)
                        |> List.rev; }

            with ex ->
                logger.FatalException ("Unable to parse the specification file.", ex)
                exit 1

        // Precompile the parsed specification to validate and process it.
        let processedSpecification, validationMessages =
            Compiler.precompile (parserSpec, options)

        // Display validation warning messages, if any.
        validationMessages.Warnings
        |> List.iter logger.Warn

        // If there are any validation _errors_ display them and abort compilation.
        match validationMessages.Errors with
        | (_ :: _) as errorMessages ->
            // Write the error messages to the console.
            errorMessages
            |> List.iter logger.Error

            1   // Exit code: Error
        | [] ->
            // Compile the processed specification.
            match Compiler.compile (processedSpecification, options) with
            | Choice2Of2 errorMessages ->
                // Write the error messages to the console.
                errorMessages
                |> List.iter logger.Error

                1   // Exit code: Error

            | Choice1Of2 parserTable ->
                // TEMP : Invoke the fsyacc-compatible backend.
                // Eventually we'll implement a way for the user to select the backend(s) to use.
                backends.FsyaccBackend.Invoke (
                    processedSpecification,
                    parserTable,
                    options)

                0   // Exit code: Success

    (* TEMP :   These defaults will be moved into the 'fsyacc'-compatible backend once we implement
                a way for the backends to "export" a list of the arguments/options they accept. *)
    //
    let [<Literal>] private defaultLexerInterpreterNamespace = "Microsoft.FSharp.Text.Lexing"
    //
    let [<Literal>] private defaultParserInterpreterNamespace = "Microsoft.FSharp.Text.Parsing"
    //
    let [<Literal>] private defaultParserModuleName = "Parser"

    /// The entry point for the application.
    [<EntryPoint; CompiledName("Main")>]
    let main (options : string[]) =
        // Variables to hold parsed command-line arguments.
        let outputPath = ref None
        let createListing = ref false
        let generatedModuleName = ref None
        let internalModule = ref false
        let openDeclarations = ResizeArray ()
        //let mlCompatible = ref false
        let lexerInterpreterNamespace = ref None
        let parserInterpreterNamespace = ref None
        let inputCodePage = ref None
        let inputFile = ref None

        /// Command-line options.
        let usage =
            [|  ArgInfo.Create ("-o", ArgType.String (fun s -> outputPath := Some s),
                    "The path where the output file will be written.");
                ArgInfo.Create ("-v", ArgType.Unit (fun () -> createListing := true),
                    "Produce a listing file.");
                ArgInfo.Create ("--module", ArgType.String (fun s -> generatedModuleName := Some s),
                    sprintf "The name to use for the F# module containing the generated parser. \
                     The default is '%s'." defaultParserModuleName);
                ArgInfo.Create ("--internal", ArgType.Unit (fun () -> internalModule := true),
                    "Generate an internal module");
                ArgInfo.Create ("--open", ArgType.String openDeclarations.Add,
                    "Add the given module to the list of those to open in both the generated signature and implementation.");
//                ArgInfo.Create ("--ml-compatibility", ArgType.Set mlCompatible,
//                    "Support the use of the global state from the 'Parsing' module in FSharp.Compatibility.OCaml.dll (available on NuGet).");
                ArgInfo.Create ("--lexlib", ArgType.String (fun s -> lexerInterpreterNamespace := Some s),
                    sprintf "Specify the namespace for the implementation of the lexer table interpreter. \
                     The default is '%s'." defaultLexerInterpreterNamespace);
                ArgInfo.Create ("--parslib", ArgType.String (fun s -> parserInterpreterNamespace := Some s),
                    sprintf "Specify the namespace for the implementation of the parser table interpreter. \
                     The default is '%s'." defaultParserInterpreterNamespace);
                ArgInfo.Create ("--codepage", ArgType.Int (fun i -> inputCodePage := Some i),
                    "Assume input lexer specification file is encoded with the given codepage.");
                |]

        // Parses argument values which aren't specified by flags.
        let plainArgParser x =
            match !inputFile with
            | None ->
                inputFile := Some x
            | Some _ ->
                // If the input filename has already been set, print a message
                // to the screen, then exit with an error code.
                printfn "Error: Only one lexer specification file may be used as input."
                exit 1

        // Parse the command-line arguments.
        ArgParser.Parse (usage, plainArgParser, "fsharpyacc <filename>")

        // Validate the parsed arguments.
        // TODO

        // If the output file is not specified, use a default value.
        if Option.isNone !outputPath then
            outputPath := Some <| System.IO.Path.ChangeExtension (Option.get !inputFile, "fs")

        // Create a CompilationOptions record from the parsed arguments
        // and call the 'invoke' function with it.
        let compilationOptions = {
            ParserType = ParserType.Lalr1;
            // TEMP
            FsyaccBackendOptions = Some {
                OutputPath = Option.get !outputPath;
                ModuleName = !generatedModuleName;
                LexerInterpreterNamespace = !lexerInterpreterNamespace;
                ParserInterpreterNamespace = !parserInterpreterNamespace;
                OpenDeclarations = openDeclarations.ToArray ();
                InternalModule = !internalModule;
                };
            }
        invoke (Option.get !inputFile) compilationOptions !inputCodePage
        

        
