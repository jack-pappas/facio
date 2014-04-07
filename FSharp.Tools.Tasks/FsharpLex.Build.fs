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
    inherit ToolTask()

    [<Required>]
    member val InputFile = null : string with get, set
    
    [<Output>]
    member val OutputFile = null : string with get, set
    
    // --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
    member val CodePage = null : string with get, set
    
    // --unicode: Produce a lexer for use with 16-bit unicode characters.
    member val Unicode = false with get, set

    member val LexLib = null : string with get, set

    // ToolTask methods
    override this.ToolName = "fsharplex.exe"
    
    override this.GenerateFullPathToTool() = System.IO.Path.Combine(this.ToolPath, this.ToolExe)
        
    override this.GenerateCommandLineCommands() =
    
        let builder = new CommandLineBuilder()
        
        // CodePage
        builder.AppendSwitchIfNotNull("--codepage ", this.CodePage)
        
        // Unicode
        if this.Unicode then builder.AppendSwitch("--unicode")

        // OutputFile
        builder.AppendSwitchIfNotNull("-o ", this.OutputFile)

        builder.AppendSwitchUnquotedIfNotNull("--lexlib ", this.LexLib)

        builder.AppendSwitchIfNotNull(" ", this.InputFile)
        
        let args = builder.ToString()

        this.BuildEngine.LogCustomEvent { new CustomBuildEventArgs(message=args,helpKeyword="",senderName="") with member x.Equals(y) = false }
        
        args
