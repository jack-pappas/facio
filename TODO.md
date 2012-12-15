## TODO

**Implement modules for generating other types of parsers**
  - Deterministic
    - SGLC -- Simple Generalized Left-Corner, accomodates SLR(1) grammars
    - XLC(1) - eXtended generalized Left-Corner(1), accomodates LR(1) grammars
	  - LAXLC(1) - Look-Ahead eXtended generalized Left-Corner(1), accomodates LALR(1) grammars
    - BC(1,1) - Bounded Context
      - Perhaps we should limit this to Bounded Right-Context (BRC) parsers?

	- Nondeterministic
	  - GLR -- Generalized LR (perhaps as Scannerless GLR (SGLR))
	  - GLC -- Generalized Left-Corner (see Nederhof, "Generalized Left-Corner Parsing")


