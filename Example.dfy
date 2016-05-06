include "Parsing.dfy"

module Example {
  import opened Parsing

  datatype SExpr = Atom(string) | List(seq<SExpr>)

  method Main() {
    // single characters
    print Parse(Digit(), "5"); // Some(5)
    print "\n";
    print Parse(Digit(), "X"); // None
    print "\n";
    var digitOrLetter: Parser<char> := Or(Digit(), Letter());
    print Parse(digitOrLetter, "X"); // Some(X)
    print "\n";
    print Parse(digitOrLetter, "+"); // None
    print "\n";

    // identifiers
    var id: Parser<string> := Seq(Letter(),
                                  ZeroOrMore(digitOrLetter),
                                  (s, ss) => [s] + ss);
    print Parse(id, "x23"); // Some(x23)
    print "\n";
    print Parse(id, "a_s"); // Some(a_s)
    print "\n";
    print Parse(id, "12a"); // None
    print "\n";

    // s-expressions
    var sexpr: Parser<SExpr> := ZComb((sexp: Parser<SExpr>)
      reads * requires forall s:string :: sexp.run.requires(s)
      => (
      var atom: Parser<SExpr> := Map(OneOrMore(digitOrLetter), s => Atom(s));
      var lst: Parser<SExpr> :=
        Skip(Then(Char('('),
                  Map(ZeroOrMore(sexp), l => List(l))),
            Char(')'));
      SkipWS(Or(atom, lst))));

    print Parse(sexpr, "x23");     // Some(Atom(x23))
    print "\n";
    print Parse(sexpr, "(a b c)"); // Some(List(Atom(a),Atom(b),Atom(c)))
    print "\n";
    print Parse(sexpr, "((a) b)"); // Some(List(List(Atom(a)),Atom(b)))
    print "\n";
    print Parse(sexpr, "((");      // None
    print "\n";

    print Parse(ZeroOrMore(sexpr), "a b c"); // Some(List(Atom(a),Atom(b),Atom(c)))
  }
}
