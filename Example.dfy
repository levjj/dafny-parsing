include "Parsing.dfy"

module Example {
  import opened Parsing

  method Main() {
    print(Parse(Digit(), "5")); // Some(5)
    print(Parse(Digit(), "X")); // None
    var digitOrLetter: Parser<char> := Or(Digit(), Letter());
    print(Parse(digitOrLetter, "X")); // Some(X)
    print(Parse(digitOrLetter, "+")); // None

  }
}
