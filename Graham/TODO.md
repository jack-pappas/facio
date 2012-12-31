## TODO (Graham)

### General

- Use our earlier, "naive" implementation of the LALR(1) table generator (which computed
  the entire LR(1) table, then merged states together) to implement unit tests for
  the the new, faster LALR(1) implementation based on DeRemer and Penello's algorithm.
  Just copy the old code out of the Git history (prior to the 'fast-lalr' branch being
  merged into 'master') and put it into the Graham.Tests project. Then, choose some
  test grammars and create the LALR(1) tables for them using both methods -- the results
  should be identical.


---
### Other Interesting Parsing Algorithms to Implement

- Deterministic
  - IELR(1) -- Inadequacy Elimination LR(1)
    - This algorithm is interesting because it provides some important advantages over
      the Canonical LR(1) algorithm employed in Menhir, mainly:
      - Provides more robust and accurate conflict resolution. Menhir uses Pager's algorithm
        to avoid the *mysterious* conflicts which can arise when merging LR(1) states to
        form LALR(1) states; however, Pager's algorithm fails to detect certain kinds of
        mysterious conflicts while the IELR(1) algorithm is able to handle them correctly.
      - Produces more efficient parsers.
  - LLC(k) - Least Left-Corner
    - Reference: *On LLC(k) Parsing Method of LR(k) Grammars* by Inoue and Fujiwara
  - SGLC -- Simple Generalized Left-Corner, accomodates SLR(1) grammars
  - XLC(1) -- eXtended generalized Left-Corner(1), accomodates LR(1) grammars
  - LAXLC(1) -- Look-Ahead eXtended generalized Left-Corner(1), accomodates LALR(1) grammars
  - LR(k,t)
  - BRC(2,1) -- Bounded Context (BRC = Bounded Right Context)

- Nondeterministic
  - GLR -- Generalized LR (perhaps as Scannerless GLR (SGLR))
  - GLC -- Generalized Left-Corner (see Nederhof, "Generalized Left-Corner Parsing")

- Miscellaneous
  - GPLR -- Generalized Piecewise LR
  - Incremental LR(1) -- "Celentano's Algorithm". This allows a file to be parsed incrementally,
    so instead of re-parsing the entire file when changes are made, only the changed portion needs
    to be parsed.
