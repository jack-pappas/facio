### Graham.Tests

* The unit-testing suite could be made much more robust if we read the test grammars and expected
  test results from files instead of having to implement it all in code.
  * Perhaps we could define some XML Schemas (*.xsd) for grammars, analysis results, and parser tables.
    It would be simple to read these in and run the tests on them, and it would be trivial to add
    new test cases (by just dropping new XML files into the folder of test cases).