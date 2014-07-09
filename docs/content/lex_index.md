FSharpLex
=========

`FSharpLex` is a tool for generating lexical analyzers ("tokenizers") from a lexer specification file (`*.fsl`).

The lexer specification files used by `FSharpLex` and the lexers it generates are largely compatible with the older `fslex` tool from the F# PowerPack. It follows a similar specification to the [OCamlLex](http://plus.kaist.ac.kr/~shoh/ocaml/ocamllex-ocamlyacc/ocamllex-tutorial/index.html) tool, though it is a reimplementation and supports some different features.

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

References
----------

This section provides references to books and academic papers detailing algorithms implemented within the `FSharpLex`(Lexing, tokenizing, and automata) projects.

Citations are presented in the Chicago style.

* Owens, Scott, John Reppy, and Aaron Turon. "Regular-expression derivatives re-examined." J. Funct. Program 19, no. 2 (2009): 173-190.
* Friedmann, Oliver, and Martin Lange. "More on balanced diets." Journal of Functional Programming 21, no. 2 (2011): 135-157.
