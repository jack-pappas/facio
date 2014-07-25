Tools for building compilers in F#
----------------------------------

This repository contains a collection of tools which assist in implementing compilers, interpreters, and other language-based tools in F#.

<div class="row">
    <div class="span1"></div>
    <div class="span6">
        <div class="well well-small" id="nuget">
            The Facio library can be <a href="https://www.nuget.org/packages/Facio/">installed from NuGet</a>:
            <pre>PM> Install-Package Facio -Pre</pre>
        </div>
    </div>
    <div class="span1"></div>
</div>

###[**FSharpLex**](/facio/lex_index.html)

`FSharpLex` is a tool for generating lexical analyzers ("tokenizers") from a lexer specification file (`*.fsl`).

The lexer specification files used by `FSharpLex` and the lexers it generates are largely compatible with the older `fslex` tool from the F# PowerPack.

###[**FSharpYacc**](/facio/yacc_index.html)

`FSharpYacc` is a tool for generating parsers for context-free grammars (CFGs) described by a parser specification file (`*.fsy`).

The parser specification files used by `FSharpYacc` and the parsers it generates are largely compatible with the older `fsyacc` tool from the F# PowerPack.

###[**Graham**](/facio/graham_index.html)

`Graham` is a library for creating, manipulating, and analyzing context-free grammars (CFGs).

`Graham` also includes algorithms for generating parser automata, providing a flexible, *generic* approach to implementing parser-generator tools like `FSharpYacc`.

Examples
-------

Example projects built on top of `Facio` compiler tools you can find in separate [Facio-Examples](https://github.com/jack-pappas/facio-examples) GitHub repository.

Implementation Status
---------------------

These tools are still in development and should be considered **alpha**-quality.

The core functionality has been implemented and passes some simple tests. The `FSharpLex` and `FSharpYacc` tools are able to bootstrap themselves, but there is still much work to be done for the user-facing parts of the code.

At this time, `FSharpLex` and `FSharpYacc` generate code which uses the lexer/parser table interpreters for fslex and fsyacc (originally provided as part of the F# PowerPack). I've copied the code for these interpreters from the [F# PowerPack repository](https://github.com/fsharp/powerpack) into the `LegacyInterpreters` project in this repository for convenience; this also allows you to build the interpreters for newer versions of .NET (the F# PowerPack was originally designed for .NET 2.0).

Licensing
---------
All projects in this repository are licensed under the terms of the [Apache 2.0 license](https://www.apache.org/licenses/LICENSE-2.0.html).
