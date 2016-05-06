include "Parsing.dfy"

module Example {
  import opened Parsing

  method Main() {
    var digitP := Parser<char>.Digit();
    var letterP := Parser<char>.Letter();
    print(digitP.Parse("5")); // Some(5)
    /* print(digitP.Parse("X")); // None */
    /* var digitOrLetterP := digitP.Or(letterP); */
    /* var digitOrLetterSeqP := digitOrLetterP.ZeroOrMore(); */

    /* var idP: Parser<string> := letterP.Then(digitOrLetterSeqP, (c, cs) => [c] + cs); */

    /* print(idP.Parse("x"));   // Some(x) */
    /* print(idP.Parse("x23")); // Some(X23) */
    /* print(idP.Parse("A_Z")); // Some(A_Z) */
    /* print(idP.Parse("12"));  // None */
  }
}
