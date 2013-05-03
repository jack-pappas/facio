F# Compiler Tools
#################

This repository contains a collection of tools which assist in implementing compilers, interpreters, and other language-based tools in F#.


Implementation Status
=====================

These tools are still in development and should be considered "alpha"-quality.

The core functionality has been implemented and passes some simple tests. The *fsharplex* and *fsharpyacc* tools are now able to bootstrap themselves. However, there is still much work to be done for the user-facing parts of the code.

At this time, both *fsharplex* and *fsharpyacc* generate code which uses the lexer/parser table interpreters for fslex and fsyacc. For the time being, I've copied the code for these interpreters from the F# PowerPack into the `LegacyInterpreters` project in this repository; this also allows you to build the interpreters for newer versions of .NET (the F# PowerPack was originally designed for .NET 2.0).

.. _`F# PowerPack repository`: https://github.com/fsharp/powerpack

fsharplex
=========

*fsharplex* is a tool for generating lexical analyzers ("tokenizers") from a lexer specification file (`*.fsl`). At this time, both the lexer specification files used by *fsharplex* and the lexers it generates are largely compatible with the older *fslex* tool from the F# PowerPack.


fsharpyacc
==========

*fsharpyacc* is a tool for generating parsers for context-free grammars (CFGs) described by a parser specification file (`*.fsy`). At this time, both the parser specification files used by *fsharpyacc* and the parsers it generates are largely compatible with the older *fsyacc* tool from the F# PowerPack.

**Compatibility Note:** When switching from *fsyacc* to *fsharpyacc*, you may find that a parser specification which works correctly with *fsyacc* does not work correctly with *fsharpyacc*. If you encounter this problem, it is likely that your parser will return a result which is not "complete" -- i.e., the parser did not parse the entire contents of the input file. The cause of this seems to be that *fsyacc* contains a bug where it sometimes does not honor a `%left` declaration for a token, meaning that some conflicts on that token may be solved by shifting (the equivalent of a `%right` declaration). The problem can be remedied by changing the `%left` declarations in question to `%right` declarations. *TODO: Include instructions for diagnosing which declarations need to be modified.*


Graham
======
*Graham* is a library for creating, manipulating, and analyzing context-free grammars (CFGs). *Graham* also includes algorithms for generating parser automata, providing a flexible, *generic* approach to implementing parser-generator tools like *fsharpyacc*.


Licensing
=========
All projects in this repository are licensed under the terms of the `Apache 2.0 license`_.

.. _`Apache 2.0 license`: http://opensource.org/licenses/Apache-2.0
