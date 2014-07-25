FSharpYacc
==========

`FSharpYacc` is a tool for generating parsers for context-free grammars (CFGs) described by a parser specification file (`*.fsy`).

The parser specification files used by `FSharpYacc` and the parsers it generates are largely compatible with the older `fsyacc` tool from the F# PowerPack. It follows a similar specification to the [OCamlYacc](http://plus.kaist.ac.kr/~shoh/ocaml/ocamllex-ocamlyacc/ocamlyacc-tutorial/index.html) parser generator (especially when used with the `ml compatibility` switch)

Compatibility Notes
-------------------

- After switching from `fsyacc` to `FSharpYacc`, you may find that a parser specification which works correctly with `fsyacc` does not work correctly with `FSharpYacc`. If you encounter this problem, it is likely that your parser will return a result which is not "complete" -- i.e., the parser did not parse the entire contents of the input file. The cause of this seems to be that `fsyacc` contains a bug where it sometimes does not honor a `%left` declaration for a token, meaning that some conflicts on that token may be solved by shifting (the equivalent of a `%right` declaration). The problem can be remedied by changing the `%left` declarations in question to `%right` declarations.

  *TODO: Include instructions for diagnosing which declarations need to be modified.*

- `FSharpYacc` handles multi-way conflicts differently than `fsyacc`. A multi-way conflict occurs when an LR parser table contains multiple REDUCE actions (and possibly, a SHIFT action) for a single LR parser state; this type of conflict often occurs when compiling a parser specification with an empty production rule for one or more nonterminals.

      The current version (as of 04-Jun-2013) of `FSharpYacc` simply discards all of the REDUCE actions except for the one with the lowest production rule number (i.e., the one which occurs closest to the top of the specification file). This stategy is "good enough" for now, but is not optimal so it will be refined in a future version.

      `fsyacc` handles multi-way conflicts on-the-fly while constructing an LR parser table. When it adds an action to an LR parser state which already contains a simple conflict (S/R or R/R), and the added action is not equal to either of the actions involved in the simple conflict, the two conflicting actions are discarded, leaving only the new action. The result of this is that the precedence and associativity declarations are not always applied to resolve conflicts, so the parser may behave unexpectedly.

Getting Started
---------------

Install the `Facio` nuget package.

<div class="row">
    <div class="span1"></div>
    <div class="span6">
        <div class="well well-small" id="nuget">
            The FSharpYacc can be <a href="https://www.nuget.org/packages/Facio/">installed from NuGet</a>:
            <pre>PM> Install-Package Facio -Pre</pre>
        </div>
    </div>
    <div class="span1"></div>
</div>


Sample input
------------

Parser generators typically produce numbers represented by values in an F# Union Type. For example:

    type Expr =
     | Val of string
     | Int of int
     | Float of float
     | Decr of Sxpr


    type Stmt =
     | Assign of string * Sxpr
     | While of Expr * Stmt
     | Seq of Stmt list
     | IfThen of Expr * Stmt
     | IfThenElse of Expr * Stmt * Stmt
     | Print of Expr


    type Prog = Prog of Stmt list

Given that, a typical parser specification is as follows:

    %{
    open Ast
    %}

    %start start
    %token <string> ID
    %token <System.Int32> INT
    %token <System.Double> FLOAT
    %token DECR LPAREN RPAREN WHILE DO END BEGIN IF THEN ELSE PRINT SEMI ASSIGN EOF
    %type < Ast.Prog > start


    %%


    start: Prog {  $1 }


    Prog: StmtList { Prog(List.rev($1)) }


    Expr: ID { Val($1) }
        | INT {  Int($1)  }
        | FLOAT {  Float($1)  }
        | DECR LPAREN Expr RPAREN {  Decr($3)  }


    Stmt: ID ASSIGN Expr { Assign($1,$3) }
        | WHILE Expr DO Stmt { While($2,$4) }
        | BEGIN StmtList END { Seq(List.rev($2)) }
        | IF Expr THEN Stmt { IfThen($2,$4) }
        | IF Expr THEN Stmt ELSE Stmt { IfThenElse($2,$4,$6) }
        | PRINT Expr { Print($2) }


    StmtList: Stmt { [$1] }
           | StmtList SEMI Stmt { $3 :: $1  }

The above generates a datatype for tokens and a function for each `start` production. Parsers are typically combined with a lexer generated using `FSharpLex`.

### MSBuild support

The nuget package includes MSBuild support for `FSharpLex` and `FSharpYacc`. You need to verify that `Facio.targets` is referenced from your project file like this (adjust the NuGet package number if needed):

    <import project="..\packages\Facio.0.8.7-alpha\build\Facio.targets"
            condition="Exists('..\packages\Facio.0.8.7-alpha\build\Facio.targets')" />

You must also add `FSharpLex` and `FSharpYacc` entries like this:

    <FSharpLex include="Lexer.fsl">
        <unicode>true</unicode>
    </FSharpLex>
    <FSharpYacc include="Parser.fsy">
        <modulename>Parser</modulename>
    </FSharpYacc>

### Command line options

    FSharpYacc <filename>

        -o <string>: Name the output file.

        -v: Produce a listing file.

        --module <string>: Define the F# module name to host the generated parser.

        --internal: Generate an internal module

        --open <string>: Add the given module to the list of those to open in both the generated signature and implementation.

        --light: (ignored)

        --light-off: Add #light "off" to the top of the generated file

        --ml-compatibility: Support the use of the global state from the 'Parsing' module in FSharp.PowerPack.dll.

        --tokens: Simply tokenize the specification file itself.

        --lexlib <string>: Specify the namespace for the implementation of the parser table interperter (default Microsoft.FSharp.Text.Parsing)

        --parslib <string>: Specify the namespace for the implementation of the parser table interperter (default Microsoft.FSharp.Text.Parsing)

        --codepage <int>: Assume input lexer specification file is encoded with the given codepage.

        --help: display this list of options

        -help: display this list of options

### Managing and using position markers

Each action in an `FsharpYacc` parser has access to a `parseState` value through which you can access position information.

    type IParseState =
        abstract InputStartPosition: int -> Position
        abstract InputEndPosition: int -> Position
        abstract InputRange: int -> Position * Position
        abstract ParserLocalStore: IDictionary<string,obj>
        abstract ResultRange  : Position * Position
        abstract RaiseError<'b> : unit -> 'b

`Input` relate to the indexes of the items on the right hand side of the current production, the `Result` relates to the entire range covered by the production. You shouldn't use `GetData` directly - these is called automatically by `$1`, `$2` etc. You can call `RaiseError` if you like.

You must set the initial position when you create the lexbuf:

    let setInitialPos (lexbuf:lexbuf) filename =
         lexbuf.EndPos <- { pos_bol = 0;
                            pos_fname=filename;
                            pos_cnum=0;
                            pos_lnum=1 }


You must also update the position recorded in the lex buffer each time you process what you consider to be a new line:

    let newline (lexbuf:lexbuf) =
        lexbuf.EndPos <- lexbuf.EndPos.AsNewLinePos()


Likewise if your language includes the ability to mark source code locations, see custom essay (e.g. the `#line` directive in OCaml and F#) then you must similarly adjust the `lexbuf.EndPos` according to the information your grok from your input.

### Notes on OCaml Compatibility

`OCamlYacc` accepts the following:

    %type < context -> context > toplevel

For `FSharpYacc` you just add parentheses:

    %type < (context -> context)) > toplevel
