=======
*Faciō*
=======
Tools for building compilers in F#
----------------------------------

.. image:: https://travis-ci.org/jack-pappas/facio.png  
    :target: https://travis-ci.org/jack-pappas/facio

.. image:: http://img.shields.io/nuget/v/facio.svg
    :target: https://nuget.org/packages/facio/

This repository contains a collection of tools which assist in implementing compilers, interpreters, and other language-based tools in F#.

- fsharplex
    ``fsharplex`` is a tool for generating lexical analyzers ("tokenizers") from a lexer specification file (``*.fsl``).

    The lexer specification files used by ``fsharplex`` and the lexers it generates are largely compatible with the older `fslex`_ tool.

- fsharpyacc
    ``fsharpyacc`` is a tool for generating parsers for context-free grammars (CFGs) described by a parser specification file (``*.fsy``).

    The parser specification files used by ``fsharpyacc`` and the parsers it generates are largely compatible with the older `fsyacc`_ tool.

- Graham
    ``Graham`` is a library for creating, manipulating, and analyzing context-free grammars (CFGs).

    ``Graham`` also includes algorithms for generating parser automata, providing a flexible, *generic* approach to implementing parser-generator tools like ``fsharpyacc``.

.. _fslex: https://github.com/fsprojects/FsLexYacc
.. _fsyacc: https://github.com/fsprojects/FsLexYacc

Implementation Status
=====================

These tools are still in development and should be considered **alpha**-quality.

The core functionality has been implemented and passes some simple tests. The ``fsharplex`` and ``fsharpyacc`` tools are able to bootstrap themselves, but there is still much work to be done for the user-facing parts of the code (e.g., providing location information when parsing fails).

At this time, ``fsharplex`` and ``fsharpyacc`` generate code which uses the lexer/parser table interpreters for ``fslex`` and ``fsyacc``. This means projects using the generated code need to reference the `FsLexYacc.Runtime`_ NuGet package.

.. _FsLexYacc.Runtime: https://github.com/fsprojects/FsLexYacc


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

Known bugs or other issues are listed on the `facio issues`_ page.

.. _`facio issues`: https://github.com/jack-pappas/facio/issues


Licensing
=========
All projects in this repository are licensed under the terms of the `Apache 2.0 license`_.

.. _`Apache 2.0 license`: https://www.apache.org/licenses/LICENSE-2.0.html
