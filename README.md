# dafny-parsing

**Parser combinator library for Dafny**

## Example

```dafny
include "Parsing.dfy"

module Example {
  import opened Parsing

  datatype SExpr = Atom(string) | List(seq<SExpr>)

  method Main() {
    // single characters
    var digit: Parser<char> := Parse.Digit();
    print digit.Parse("5"); // Some(5)
    print digit.Parse("X"); // None
    var digitOrLetter: Parser<char> := digit.Or(Parse.Letter());
    print digitOrLetter.Parse("X"); // Some(X)
    print digitOrLetter.Parse("+"); // None

    // identifiers
    var id: Parser<string> := Parse.Letter().Seq(
                                  digitOrLetter.ZeroOrMore(),
                                  (c: char, s: string) => [c] + s);
    print id.Parse("x23"); // Some(x23)
    print id.Parse("a_s"); // Some(a_s)
    print id.Parse("12a"); // None

    // s-expressions
    var sexpr: Parser<SExpr> := Parse.Fix((sexp: Parser<SExpr>) requires sexp != null => (
      var atom: Parser<SExpr> := digitOrLetter.OneOrMore().Map(s => Atom(s));
      var lst: Parser<SExpr> :=
           Parse.Char('(')
             .Then(sexp.ZeroOrMore().Map(l => List(l)))
             .Skip(Parse.Char(')'));
      atom.Or(lst).SkipWS()));

    print sexpr.Parse("x23");     // Some(Atom(x23))
    print sexpr.Parse("(a b c)"); // Some(List(Atom(a),Atom(b),Atom(c)))
    print sexpr.Parse("((a) b)"); // Some(List(List(Atom(a)),Atom(b)))
    print sexpr.Parse("((");      // None
  }
}
```

A frist version of this library was implemented in pure Dafny using algebraic
datatypes and functions. However, recursive parsing requires either late
binding for closures or a fixpoint combinator. The latter was implemented
correctly but simple examples caused Dafny to timeout due to the nested
requirements of anonymous functions.

Therefore, the current version is written mostly in C# with a Dafny-specific
interface and a class/method-based API.
