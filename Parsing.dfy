module Parsing {
  class Option<A> {
    extern function method IsNone(): bool
    extern function method Val(): A
  }
  class Parser<A> {
    extern function method Map<B>(f: A -> B): Parser<B>
    ensures Map(f) != null

    extern function method Or(p2: Parser<A>): Parser<A>
    requires p2 != null
    ensures Or(p2) != null

    extern function method Bind<B>(f: A -> Parser<B>): Parser<B>
    ensures Bind(f) != null

    extern function method Seq<B,C>(pb: Parser<B>, f: (A, B) -> C): Parser<C>
    requires pb != null
    ensures Seq(pb, f) != null

    extern function method Seq3<B,C,D>(pb: Parser<B>, pc: Parser<C>, f: (A, B, C) -> D): Parser<D>
    requires pb != null
    requires pc != null
    ensures Seq3(pb, pc, f) != null

    extern function method Skip<B>(pb: Parser<B>): Parser<A>
    requires pb != null
    ensures Skip(pb) != null

    extern function method Then<B>(pb: Parser<B>): Parser<B>
    requires pb != null
    ensures Then(pb) != null

    extern function method SkipWS(): Parser<A>
    ensures SkipWS() != null

    extern function method ZeroOrMore(): Parser<seq<A>>
    ensures ZeroOrMore() != null

    extern function method OneOrMore(): Parser<seq<A>>
    ensures OneOrMore() != null

    extern function method Parse(str: string): Option<A>
    ensures Parse(str) != null

    extern function method ParseFile(filename: array<char>): Option<A>
    ensures ParseFile(filename) != null

    extern function method ParseCmdLine(): Option<A>
    ensures ParseCmdLine() != null
  }
  class Parse {
    extern static function method Const<A>(a: A): Parser<A>
    ensures Const(a) != null

    extern static function method SatChar(pred: char -> bool): Parser<char>
    ensures SatChar(pred) != null

    extern static function method Char(c2: char): Parser<char>
    ensures Char(c2) != null

    extern static function method Digit(): Parser<char>
    ensures Digit() != null

    extern static function method Letter(): Parser<char>
    ensures Letter() != null

    extern static function method Decimal(): Parser<int>
    ensures Decimal() != null

    extern static function method Keyword(str: string): Parser<string>
    ensures Keyword(str) != null

    extern static function method Fix<A>(f: Parser<A> -> Parser<A>): Parser<A>
    ensures Fix(f) != null
  }
}
