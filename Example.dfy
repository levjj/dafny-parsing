include "Parsing.dfy"

module Example {
  import opened Parsing

  method Main() {
    print(Parse(DigitP(), "5")); // Some(5)
    print(Parse(DigitP(), "X")); // None
    print(Parse(OrP(DigitP(), LetterP()), "X")); // Some(X)
    print(Parse(OrP(DigitP(), LetterP()), "+")); // None
  }
}
