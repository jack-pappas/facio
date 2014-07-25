FSharpLex
=========

`FSharpLex` is a tool for generating lexical analyzers ("tokenizers") from a lexer specification file (`*.fsl`).

The lexer specification files used by `FSharpLex` and the lexers it generates are largely compatible with the older `fslex` tool from the F# PowerPack. It follows a similar specification to the [OCamlLex](http://plus.kaist.ac.kr/~shoh/ocaml/ocamllex-ocamlyacc/ocamllex-tutorial/index.html) tool, though it is a reimplementation and supports some different features.

Getting Started
---------------

Install the `Facio` nuget package.

<div class="row">
    <div class="span1"></div>
    <div class="span6">
        <div class="well well-small" id="nuget">
            The FSharpLex can be <a href="https://www.nuget.org/packages/Facio/">installed from NuGet</a>:
            <pre>PM> Install-Package Facio -Pre</pre>
        </div>
    </div>
    <div class="span1"></div>
</div>

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

### Sample input


This is taken from the `Parsing` sample previously in the F# distribution. See below for information on `newline` and line counting.

    let digit = ['0'-'9']
    let whitespace = [' ' '\t' ]
    let newline = ('\n' | '\r' '\n')


    rule token = parse
    | whitespace     { token lexbuf }
    | newline        { newline lexbuf; token lexbuf }
    | "while"        { WHILE }
    | "begin"        { BEGIN }
    | "end"          { END }
    | "do"           { DO }
    | "if"           { IF }
    | "then"         { THEN }
    | "else"         { ELSE }
    | "print"        { PRINT }
    | "decr"         { DECR }
    | "("            { LPAREN }
    | ")"            { RPAREN }
    | ";"            { SEMI }
    | ":="           { ASSIGN }
    | ['a'-'z']+     { ID(lexeme lexbuf) }
    | ['-']?digit+   { INT (Int32.Parse(lexeme lexbuf)) }
    | ['-']?digit+('.'digit+)?(['e''E']digit+)?   { FLOAT (Double.Parse(lexeme lexbuf)) }
    | eof            { EOF }


More than one lexer state is permitted - use

    rule state1 =
     | "this"    { state2 lexbuf }
     | ...
    and state2 =
     | "that"    { state1 lexbuf }
     | ...


States can be passed arguments:

    rule state1 arg1 arg2 = ...
     | "this"    { state2 (arg1+1) (arg2+2) lexbuf }
     | ...
    and state2 arg1 arg2 = ...
     | ...



### Using a lexer

If in the first example above the constructors `INT` etc generate values of type `tok` then the above generates a lexer with a function

    val token : LexBuffer<byte> -> tok

Once you have a lexbuffer you can call the above to generate new tokens. Typically you use some methods from `Microsoft.FSharp.Text.Lexing` to create lex buffers, either a `LexBuffer<byte>` for ASCII lexing, or `LexBuffer<char>` for Unicode lexing.

Some ways of creating lex buffers are by using:

    LexBuffer<_>.FromChars
    LexBuffer<_>.FromFunction
    LexBuffer<_>.FromStream
    LexBuffer<_>.FromTextReader
    LexBuffer<_>.FromArray

Within lexing actions the variable `lexbuf` is in scope and you may use properties on the `LexBuffer` type such as:

    lexbuf.Lexeme                 // get the lexeme as an array of characters or bytes
    LexBuffer.LexemeString lexbuf // get the lexeme as a string, for Unicode lexing

Lexing positions give locations in source files (the relevant type is `Microsoft.FSharp.Text.Lexing.Position`).

Generated lexers are nearly always used in conjunction with parsers generarted by `FSharpYacc`(also documented on this site). See the Parsed Language starter template.

 Command line options

    fsahrplex <filename>
        -o <string>: Name the output file.

        --codepage <int>: Assume input lexer specification file is encoded with the given codepage.

        --light: (ignored)

        --light-off: Add #light "off" to the top of the generated file

        --lexlib <string>: Specify the namespace for the implementation of the lexer table interperter (default Microsoft.FSharp.Text.Lexing)

        --unicode: Produce a lexer for use with 16-bit unicode characters.

        --help: display this list of options

        -help: display this list of options

Positions and line counting in lexers

Within a lexer lines can in theory be counted simply by incrementing a global variable or a passed line number count:

    rule token line = ...
     | "\n" | '\r' '\n'    { token (line+1) }
     | ...

However for character positions this is tedious, as it means every action becomes polluted with character counting, as you have to manually attach line numbers to tokens. Also, for error reporting writing service it is useful to have to have position information associated held as part of the state in the lexbuffer itself.

Thus Facio follows the `OCamlLex` model where the lexer and parser state carry `position` values that record information for the current match (`lex`) and the `l.h.s`/`r.h.s` of the grammar productions (`yacc`).

The information carried for each position is:

 * a filename
 * a current 'absolute' character number
 * a placeholder for a user-tracked beginning-of-line marker
 * a placeholder for a user-tracked line number count.

### Passing state through lexers


It is sometimes under-appreciated that you can pass arguments around between lexer states. For example, in one example we used imperative state to track a line number.

    let current_line = ref 0
    let current_char = ref 0
    let set_next_line lexbuf = ..

    ...
    rule main = parse
      | ...
      | "//" [^ '\n']* '\n' {
           set_next_line lexbuf; main lexbuf
        }


This sort of imperative code is better replaced by passing arguments:

    rule main line char = parse
      | ...
      | "//" [^ '\n']* '\n' {
           main (line+1) 0 lexbuf
        }

A good example is that when lexing a comment you want to pass through the start-of-comment position so that you can give a good error message if no end-of-comment is found. Or likewise you may want to pass through the number of nested of comments.


References
----------

This section provides references to books and academic papers detailing algorithms implemented within the `FSharpLex`(Lexing, tokenizing, and automata) projects.

Citations are presented in the Chicago style.

* Owens, Scott, John Reppy, and Aaron Turon. "Regular-expression derivatives re-examined." J. Funct. Program 19, no. 2 (2009): 173-190.
* Friedmann, Oliver, and Martin Lange. "More on balanced diets." Journal of Functional Programming 21, no. 2 (2011): 135-157.
