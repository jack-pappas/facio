// (c) Microsoft Corporation 2005-2009.

namespace Microsoft.FSharp.Build

open System
open Microsoft.Build.Framework
open Microsoft.Build.Utilities

(**************************************
MSBuild task for fsharplex

options:
        -o <string>: Name the output file.
        --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
        --unicode: Produce a lexer for use with 16-bit unicode characters.
        --help: display this list of options
        -help: display this list of options
**************************************)

type FsLex() = 
    inherit ToolTask()

    // [<Required>]
    member val InputFile = "" with get, set
    
    [<Output>]
    member val OutputFile = "" with get, set
    
    // --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
    member val CodePage = "" with get, set
    
    // --unicode: Produce a lexer for use with 16-bit unicode characters.
    member val Unicode = false with get, set

    member val OtherFlags = "" with get, set

    // ToolTask methods
    override this.ToolName = "fslex.exe"
    
    override this.GenerateFullPathToTool() = System.IO.Path.Combine(this.ToolPath, this.ToolExe)
        
    override this.GenerateCommandLineCommands() =
    
        let builder = new CommandLineBuilder()
        
        // CodePage
        builder.AppendSwitchIfNotNull("--codepage ", this.CodePage)
        
        // Unicode
        if this.Unicode then builder.AppendSwitch("--unicode")

        // OutputFile
        builder.AppendSwitchIfNotNull("-o ", this.OutputFile)

        // OtherFlags - must be second-to-last
        builder.AppendSwitchUnquotedIfNotNull("", this.OtherFlags)

        builder.AppendSwitchIfNotNull(" ", this.InputFile)
        
        let args = builder.ToString()

        // when doing simple unit tests using API, no BuildEnginer/Logger is attached
        if this.BuildEngine <> null then
            let eventArgs = { new CustomBuildEventArgs(message=args,helpKeyword="",senderName="") with member x.Equals(y) = false }
            this.BuildEngine.LogCustomEvent(eventArgs)
        args
