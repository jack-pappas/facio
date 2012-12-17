## TODO (FSharpYacc)

### General

- It might be possible to simplify the code in the FSharpYacc.LR namespace (`LR.fs`)
  by defining an interface with generic parameters for `'Nonterminal`, `'Terminal`,
  and `'Lookahead` and methods which manipulate an `LrTableGenState` of the appropriate
  type. Then, define types (or use object expressions) which implement this interface
  for various grammar classes, e.g., LR(0), SLR(1), LR(1). Finally, we should be able
  to implement a worklist-based loop which uses some instance of this interface to
  create the parser states from the grammar. (NOTE : Instead of implementing this from
  scratch, we'll just modify one of the existing worklist loops.)


---
### Implement modules for generating other types of parsers

- Deterministic
  - IELR(1) -- Inadequacy Elimination LR(1)
    - This algorithm is interesting because it provides some important advantages over
      the Canonical LR(1) algorithm employed in Menhir, mainly:
      - Provides more robust and accurate conflict resolution. Menhir uses Pager's algorithm
        to avoid the *mysterious* conflicts which can arise when merging LR(1) states to
        form LALR(1) states; however, Pager's algorithm fails to detect certain kinds of
        mysterious conflicts while the IELR(1) algorithm is able to handle them correctly.
      - Produces more efficient parsers.
  - SGLC -- Simple Generalized Left-Corner, accomodates SLR(1) grammars
  - XLC(1) -- eXtended generalized Left-Corner(1), accomodates LR(1) grammars
  - LAXLC(1) -- Look-Ahead eXtended generalized Left-Corner(1), accomodates LALR(1) grammars
  - BC(1,1) -- Bounded Context
    - Perhaps we should limit this to Bounded Right-Context (BRC) parsers?

- Nondeterministic
  - GLR -- Generalized LR (perhaps as Scannerless GLR (SGLR))
  - GLC -- Generalized Left-Corner (see Nederhof, "Generalized Left-Corner Parsing")

