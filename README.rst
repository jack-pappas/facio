F# Compiler Tools
#################

This repository contains a collection of tools which assist in implementing compilers, interpreters, and other language-based tools in F#.

- fsharplex

    ``fsharplex`` is a tool for generating lexical analyzers ("tokenizers") from a lexer specification file (``*.fsl``).

    The lexer specification files used by ``fsharplex`` and the lexers it generates are largely compatible with the older ``fslex`` tool from the F# PowerPack.

- fsharpyacc

    ``fsharpyacc`` is a tool for generating parsers for context-free grammars (CFGs) described by a parser specification file (``*.fsy``).

    The parser specification files used by ``fsharpyacc`` and the parsers it generates are largely compatible with the older ``fsyacc`` tool from the F# PowerPack.

- Graham

    ``Graham`` is a library for creating, manipulating, and analyzing context-free grammars (CFGs).

    ``Graham`` also includes algorithms for generating parser automata, providing a flexible, *generic* approach to implementing parser-generator tools like ``fsharpyacc``.


Implementation Status
=====================

These tools are still in development and should be considered **alpha**-quality.

The core functionality has been implemented and passes some simple tests. The ``fsharplex`` and ``fsharpyacc`` tools are able to bootstrap themselves, but there is still much work to be done for the user-facing parts of the code.

At this time, ``fsharplex`` and ``fsharpyacc`` generate code which uses the lexer/parser table interpreters for fslex and fsyacc (originally provided as part of the F# PowerPack). I've copied the code for these interpreters from the `F# PowerPack repository` into the `LegacyInterpreters` project in this repository for convenience; this also allows you to build the interpreters for newer versions of .NET (the F# PowerPack was originally designed for .NET 2.0).

.. _`F# PowerPack repository`: https://github.com/fsharp/powerpack


Compatibility Notes
===================

- fsharpyacc

    - After switching from ``fsyacc`` to ``fsharpyacc``, you may find that a parser specification which works correctly with ``fsyacc`` does not work correctly with ``fsharpyacc``. If you encounter this problem, it is likely that your parser will return a result which is not "complete" -- i.e., the parser did not parse the entire contents of the input file. The cause of this seems to be that ``fsyacc`` contains a bug where it sometimes does not honor a ``%left`` declaration for a token, meaning that some conflicts on that token may be solved by shifting (the equivalent of a ``%right`` declaration). The problem can be remedied by changing the ``%left`` declarations in question to ``%right`` declarations.

      *TODO: Include instructions for diagnosing which declarations need to be modified.*

    - ``fsharpyacc`` handles multi-way conflicts differently than ``fsyacc``. A multi-way conflict occurs when an LR parser table contains multiple REDUCE actions (and possibly, a SHIFT action) for a single LR parser state; this type of conflict often occurs when compiling a parser specification with an empty production rule for one or more nonterminals.

      The current version (as of 04-Jun-2013) of ``fsharpyacc`` simply discards all of the REDUCE actions except for the one with the lowest production rule number (i.e., the one which occurs closest to the top of the specification file). This stategy is "good enough" for now, but is not optimal so it will be refined in a future version.

      ``fsyacc`` handles multi-way conflicts on-the-fly while constructing an LR parser table. When it adds an action to an LR parser state which already contains a simple conflict (S/R or R/R), and the added action is not equal to either of the actions involved in the simple conflict, the two conflicting actions are discarded, leaving only the new action. The result of this is that the precedence and associativity declarations are not always applied to resolve conflicts, so the parser may behave unexpectedly.


Known Bugs/Issues
=================

- fsharplex

    - There is a performance issue which arises when compiling a lexer specification which makes heavy use of Unicode character classes (such as the lexer for the F# compiler). Due to the way ``fsharplex`` is designed, the comparison function for the CharSet data structure is called repeatedly; the Unicode character classes use CharSet extensively, and the CharSet comparison function has a relatively heavyweight implementation, so the combination of these factors causes a blowup in execution time which causes ``fsharplex`` to take an extremely long time to compile the lexer specification. For example, profiling ``fsharplex`` when compiling the lexer for the F# compiler shows that most (>90%) of the execution time is spent within the CharSet comparison function. Eventually, this issue will be fixed by modifying the CharSet implementation itself to allow a much faster comparison function to be used.

- fsharpyacc / Graham

    - Some parts of the LR (LR(0), SLR(1), LALR(1), LR(1)) parser table generation have not been optimized yet. This issue doesn't impact smaller parser specifications, but larger specifications such as the parser for the F# compiler can take a long time to compile. The parts of the code causing the performance drain will eventually be profiled and tuned to correct the problem; the likely solution will be to implement memoization in some places, and to increase the performance of some Map lookups by using TagBimap to assign 'tags' which can be used in place of more heavyweight objects (e.g., LrParserState<_,_,_>).


Licensing
=========
All projects in this repository are licensed under the terms of the `Apache 2.0 license`_.

.. _`Apache 2.0 license`: http://opensource.org/licenses/Apache-2.0
