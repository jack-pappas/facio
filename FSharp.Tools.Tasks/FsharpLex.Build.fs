// (c) Microsoft Corporation 2005-2009.

namespace FSharp.Tools.Tasks

open System
open Microsoft.Build.Framework
open Microsoft.Build.Utilities

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

type FsharpLex() = 
    inherit Task()   
    //do this.StandardOutputImportance <- "Normal"
    [<Required>]
    member val InputFile = null : string with get, set
    
    [<Output>]
    member val OutputFile = null : string with get, set
    
    // --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
    member val CodePage = null : string with get, set
    
    // --unicode: Produce a lexer for use with 16-bit unicode characters.
    member val Unicode = false with get, set

    member val LexLib = null : string with get, set
        
    override this.Execute() =
        BuildLogger.logger <- this.Log
        BuildLogger.file <- this.InputFile

        let toOption x = if x = null then None else Some x
        FSharpLex.Program.inputFile := toOption this.InputFile
        FSharpLex.Program.outputFile := toOption this.OutputFile
        if this.LexLib <> null then FSharpLex.Program.lexlib := this.LexLib
        FSharpLex.Program.unicode := this.Unicode
        let success, codePage = Int32.TryParse this.CodePage
        if success then FSharpLex.Program.inputCodePage := Some codePage

        let logger = NLog.LogManager.GetCurrentClassLogger()
        logger.Info "Running FSharpLex..."

        FSharpLex.Program.main [| |] = 0