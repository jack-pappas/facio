## F# Compiler Tools ##

This repository contains a collection of tools which assist in implementing compilers, interpreters, and other language-based tools in F#.


### Implementation Status
---
These tools are still in development and should be considered "alpha"-quality. The core functionality has been implemented and passes some simple tests; the **fsharplex** and **fsharpyacc** tools are now also able to bootstrap themselves. However, there is much work remaining to be done as far as implementing the user-facing parts of the code.

At this time, both **fsharplex** and **fsharpyacc** generate code which uses the lexer/parser table interpreters from the F# PowerPack. This means you'll need to clone the [F# PowerPack repository](https://github.com/fsharp/powerpack) and build the `FSharp.PowerPack` assembly, making sure to change the target framework version (in the project settings) to the *exact same*  framework version used by your own project. Failure to do this will cause your lexers/parsers to fail at runtime with unusual and hard-to-track-down exceptions (e.g., `MissingMethodExeption`).


### fsharplex
---
**fsharplex** is a tool for generating lexical analyzers ("tokenizers") from a lexer specification file (`*.fsl`). At this time, both the lexer specification files used by **fsharplex** and the lexers it generates are largely compatible with the older *fslex* tool from the F# PowerPack.


### fsharpyacc
---
**fsharpyacc** is a tool for generating parsers for context-free grammars (CFGs) described by a parser specification file (`*.fsy`). At this time, both the parser specification files used by **fsharpyacc** and the parsers it generates are largely compatible with the older *fsyacc* tool from the F# PowerPack.


### Graham
---
**Graham** is a library for creating, manipulating, and analyzing context-free grammars (CFGs). **Graham** also includes algorithms for generating parser automata, providing a flexible, *generic* approach to implementing parser-generator tools like ***fsharpyacc***.


### Licensing
---
All projects in this repository are licensed under permissive licenses; at this time, that means either the [Modified (2-clause) BSD license](http://opensource.org/licenses/BSD-2-Clause) or the [Apache 2.0 license](http://opensource.org/licenses/Apache-2.0).
