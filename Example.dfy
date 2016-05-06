include "Parsing.dfy"

module Example {
  import opened Parsing

  datatype SExpr = Atom(string) | List(seq<SExpr>)

  method Main() {
    // single characters
    print(Parse(Digit(), "5")); // Some(5)
    print(Parse(Digit(), "X")); // None
    var digitOrLetter: Parser<char> := Or(Digit(), Letter());
    print(Parse(digitOrLetter, "X")); // Some(X)
    print(Parse(digitOrLetter, "+")); // None

    // identifiers
    var id: Parser<string> := Seq(Letter(),
                                  ZeroOrMore(digitOrLetter),
                                  (s, ss) => [s] + ss);
    print(Parse(id, "x23")); // Some(x23)
    print(Parse(id, "a_s")); // Some(a_s)
    print(Parse(id, "12a")); // None

    // s-expressions
    var atom: Parser<SExpr> :=
      Map(SkipOptional(OneOrMore(digitOrLetter), Char(' ')),
          s => Atom(s));
    var sexpr: Parser<SExpr> := atom;
    sexpr :=
      Or(atom,
         Map(Skip(Then(Char('('), ZeroOrMore(atom)), Char(')')),
             l => List(l)));

    print(Parse(sexpr, "x23"));     // Some(Atom(x23))
    print("\n");
    print(Parse(sexpr, "(a b c)")); // Some(List(Atom(a),Atom(b),Atom(c)))
    print("\n");
    print(Parse(sexpr, "((a) b)")); // Some(List(List(Atom(a)),Atom(b)))
    print("\n");
    print(Parse(sexpr, "(("));      // None
  }
}
