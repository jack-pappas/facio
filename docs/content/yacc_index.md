FSharpYacc
==========

`FSharpYacc` is a tool for generating parsers for context-free grammars (CFGs) described by a parser specification file (`*.fsy`).

The parser specification files used by `FSharpYacc` and the parsers it generates are largely compatible with the older `fsyacc` tool from the F# PowerPack. It follows a similar specification to the [OCamlYacc](http://plus.kaist.ac.kr/~shoh/ocaml/ocamllex-ocamlyacc/ocamlyacc-tutorial/index.html) parser generator (especially when used with the `ml compatibility` switch)

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

Compatibility Notes
-------------------

- After switching from `fsyacc` to `FSharpYacc`, you may find that a parser specification which works correctly with `fsyacc` does not work correctly with `FSharpYacc`. If you encounter this problem, it is likely that your parser will return a result which is not "complete" -- i.e., the parser did not parse the entire contents of the input file. The cause of this seems to be that `fsyacc` contains a bug where it sometimes does not honor a `%left` declaration for a token, meaning that some conflicts on that token may be solved by shifting (the equivalent of a `%right` declaration). The problem can be remedied by changing the `%left` declarations in question to `%right` declarations.

  *TODO: Include instructions for diagnosing which declarations need to be modified.*

- `FSharpYacc` handles multi-way conflicts differently than `fsyacc`. A multi-way conflict occurs when an LR parser table contains multiple REDUCE actions (and possibly, a SHIFT action) for a single LR parser state; this type of conflict often occurs when compiling a parser specification with an empty production rule for one or more nonterminals.

      The current version (as of 04-Jun-2013) of `FSharpYacc` simply discards all of the REDUCE actions except for the one with the lowest production rule number (i.e., the one which occurs closest to the top of the specification file). This stategy is "good enough" for now, but is not optimal so it will be refined in a future version.

      `fsyacc` handles multi-way conflicts on-the-fly while constructing an LR parser table. When it adds an action to an LR parser state which already contains a simple conflict (S/R or R/R), and the added action is not equal to either of the actions involved in the simple conflict, the two conflicting actions are discarded, leaving only the new action. The result of this is that the precedence and associativity declarations are not always applied to resolve conflicts, so the parser may behave unexpectedly.