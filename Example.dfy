include "Parsing.dfy"

module Example {
  import opened Parsing

  datatype SExpr = Atom(string) | List(seq<SExpr>)

  method Main() {
    // single characters
    var digit: Parser<char> := Parse.Digit();
    print digit.Parse("5"); // Some(5)
    print "\n";
    print digit.Parse("X"); // None
    print "\n";
    var digitOrLetter: Parser<char> := digit.Or(Parse.Letter());
    print digitOrLetter.Parse("X"); // Some(X)
    print "\n";
    print digitOrLetter.Parse("+"); // None
    print "\n";

    // identifiers
    var id: Parser<string> := Parse.Letter().Seq(
                                  digitOrLetter.ZeroOrMore(),
                                  (c: char, s: string) => [c] + s);
    print id.Parse("x23"); // Some(x23)
    print "\n";
    print id.Parse("a_s"); // Some(a_s)
    print "\n";
    print id.Parse("12a"); // None
    print "\n";

    // s-expressions
    var sexpr: Parser<SExpr> := Parse.Fix((sexp: Parser<SExpr>) requires sexp != null => (
      var atom: Parser<SExpr> := digitOrLetter.OneOrMore().Map(s => Atom(s));
      var lst: Parser<SExpr> :=
           Parse.Char('(')
             .Then(sexp.ZeroOrMore().Map(l => List(l)))
             .Skip(Parse.Char(')'));
      atom.Or(lst).SkipWS()));

    print sexpr.Parse("x23");     // Some(Atom(x23))
    print "\n";
    print sexpr.Parse("(a b c)"); // Some(List(Atom(a),Atom(b),Atom(c)))
    print "\n";
    print sexpr.Parse("((a) b)"); // Some(List(List(Atom(a)),Atom(b)))
    print "\n";
    print sexpr.Parse("((");      // None
    print "\n";
  }
}
