module Parsing {
  datatype Parser<A> = Parser(run: string -> seq<(A, string)>)

  datatype Option<A> = Some(some: A) | None

  module Helpers {
    function method Map<A,B>(a: seq<A>, f: A -> B): seq<B>
    reads f.reads;
    requires forall x: A :: f.requires(x)
    {
      if |a| == 0 then []
                  else [f(a[0])] + Map<A,B>(a[1..], f)
    }

    function method Flatten<A>(a: seq<seq<A>>): seq<A>
    {
      if |a| == 0 then []
                  else a[0] + Flatten(a[1..])
    }

    class FileSystem {
      extern static method ReadFile(name:array<char>) returns (contents: array<char>)
    }
  }

  function method Const<A>(a: A): Parser<A>
  ensures forall s:string :: Const(a).run.requires(s);
  ensures forall s:string :: Const(a).run.reads(s) == {};
  {
    Parser(s => [(a, s)])
  }

  function method Map<A,B>(p: Parser<A>, f: A -> B): Parser<B>
  reads *;
  requires forall a: A :: f.requires(a);
  requires forall s:string :: p.run.requires(s);
  ensures forall s:string :: Map(p, f).run.requires(s);
  {
    Parser((s: string) reads *
                       requires p.run.requires(s)
                       requires forall a: A :: f.requires(a)
                       => Helpers.Map(p.run(s),
                                      (a_s: (A, string)) reads f.reads
                                      requires forall a: A :: f.requires(a)
                                      => (f(a_s.0), a_s.1)))
  }

  function method SatChar(pred: char -> bool): Parser<char>
  reads pred.reads;
  requires forall c:char :: pred.requires(c);
  ensures forall s:string :: SatChar(pred).run.requires(s);
  ensures forall s:string :: SatChar(pred).run.reads(s) <= if |s| > 0 then pred.reads(s[0]) else {};
  {
    Parser((s: string) reads if |s| > 0 then pred.reads(s[0]) else {}
                       requires |s| > 0 ==> pred.requires(s[0])
                       => if |s| == 0 then []
                          else if pred(s[0]) then [(s[0], s[1..])]
                          else [])
  }

  function method Or<A>(p1: Parser<A>, p2: Parser<A>): Parser<A>
  reads p1.run.reads;
  reads p2.run.reads;
  requires forall s:string :: p1.run.requires(s);
  requires forall s:string :: p2.run.requires(s);
  ensures forall s:string :: Or(p1, p2).run.requires(s);
  ensures forall s:string :: Or(p1, p2).run.reads(s) ==
    (set s,o | o in p1.run.reads(s) + p2.run.reads(s) :: o)
  {
    Parser((s: string) reads p1.run.reads reads p2.run.reads
                       requires p1.run.requires(s) requires p2.run.requires(s)
                       => p1.run(s) + p2.run(s))
  }

  function method Char(c: char): Parser<char>
  ensures forall s:string :: Char(c).run.requires(s);
  ensures forall s:string :: Char(c).run.reads(s) == {};
  {
    SatChar(c2 => c == c2)
  }

  function method Digit(): Parser<char>
  ensures forall s:string :: Digit().run.requires(s);
  ensures forall s:string :: Digit().run.reads(s) == {};
  {
    SatChar(c => '0' <= c <= '9')
  }

  function method Letter(): Parser<char>
  ensures forall s:string :: Letter().run.requires(s);
  ensures forall s:string :: Letter().run.reads(s) == {};
  {
    SatChar(c => 'A' <= c <= 'Z' || 'a' <= c <= 'z' || c == '_')
  }

  function method Bind<A,B>(pa: Parser<A>, pb: A -> Parser<B>): Parser<B>
  reads *;
  requires forall s:string :: pa.run.requires(s);
  requires forall a:A :: pb.requires(a);
  requires forall a:A, s:string :: pb(a).run.requires(s);
  ensures forall s:string :: Bind(pa, pb).run.requires(s);
  {
    Parser((s: string)
                  reads *
                  requires pa.run.requires(s)
                  requires forall a: A :: pb.requires(a)
                  requires forall a: A, s: string :: pb(a).run.requires(s) =>
    (
      var par: seq<(A, string)> := pa.run(s);
      var pcomb: seq<seq<(B, string)>> := Helpers.Map(par, (a_s: (A, string))
                      reads *
                      requires forall a:A :: pb.requires(a)
                      requires forall a:A, s:string :: pb(a).run.requires(s)
                      => pb(a_s.0).run(a_s.1));
      Helpers.Flatten(pcomb)
    ))
  }

  function method Seq<A,B,C>(pa: Parser<A>, pb: Parser<B>, f: (A,B) -> C): Parser<C>
  reads *;
  requires forall a:A, b: B :: f.requires(a,b);
  requires forall s:string :: pa.run.requires(s);
  requires forall s:string :: pb.run.requires(s);
  ensures forall s:string :: Seq(pa, pb, f).run.requires(s);
  {
    var cont: A -> B -> Parser<C> :=
      (a: A) reads *
             requires forall b: B :: f.requires(a,b)
             => (b: B) reads *
                       requires f.requires(a,b)
                       => Const(f(a,b));
    Bind<A,C>(pa, (a: A) reads *
                         requires forall a:A, b: B :: f.requires(a,b)
                         requires forall s:string :: pb.run.requires(s)
                         => Bind<B,C>(pb, cont(a)))
  }

  function method Skip<A,B>(pa: Parser<A>, pb: Parser<B>): Parser<A>
  reads *;
  requires forall s:string :: pa.run.requires(s);
  requires forall s:string :: pb.run.requires(s);
  ensures forall s:string :: Skip(pa, pb).run.requires(s);
  {
    Seq<A,B,A>(pa, pb, (a, b) => a)
  }

  function method Then<A,B>(pa: Parser<A>, pb: Parser<B>): Parser<B>
  reads *;
  requires forall s:string :: pa.run.requires(s);
  requires forall s:string :: pb.run.requires(s);
  ensures forall s:string :: Then(pa, pb).run.requires(s);
  {
    Seq<A,B,B>(pa, pb, (a, b) => b)
  }

  function method SkipOptional<A,B>(pa: Parser<A>, pb: Parser<B>): Parser<A>
  reads *;
  requires forall s:string :: pa.run.requires(s);
  requires forall s:string :: pb.run.requires(s);
  ensures forall s:string :: Skip(pa, pb).run.requires(s);
  {
    Or(Skip(pa, pb), pa)
  }

  function method ZeroOrMoreLim<A>(p: Parser<A>, limit: nat): Parser<seq<A>>
  reads *;
  requires forall s:string :: p.run.requires(s);
  ensures forall s:string :: ZeroOrMoreLim(p, limit).run.requires(s);
  decreases limit
  {
    if limit == 0
    then Const([])
    else Or(OneOrMoreLim<A>(p, limit - 1), Const([]))
  }

  function method OneOrMoreLim<A>(p: Parser<A>, limit: nat): Parser<seq<A>>
  reads *;
  requires forall s:string :: p.run.requires(s);
  ensures forall s:string :: OneOrMoreLim(p, limit).run.requires(s);
  decreases limit
  {
    if limit == 0
    then Const([])
    else Seq<A, seq<A>, seq<A>>(p, ZeroOrMoreLim(p, limit - 1), (a, aa) => [a] + aa)
  }

  function method OneOrMore<A>(p: Parser<A>): Parser<seq<A>>
  reads *;
  requires forall s:string :: p.run.requires(s);
  ensures forall s:string :: OneOrMore(p).run.requires(s);
  {
    ZeroOrMoreLim(p, 1000)
  }

  function method ZeroOrMore<A>(p: Parser<A>): Parser<seq<A>>
  reads *;
  requires forall s:string :: p.run.requires(s);
  ensures forall s:string :: ZeroOrMore(p).run.requires(s);
  {
    OneOrMoreLim(p, 1000)
  }

  function method Lazy<A>(f: () -> Parser<A>): Parser<A>
  reads *;
  requires f.requires();
  requires forall s:string :: f().run.requires(s);
  ensures forall s:string :: Lazy(f).run.requires(s);
  {
    Parser((s: string) reads *
                       requires f.requires()
                       requires f().run.requires(s)
                       => f().run(s))
  }

  function method Parse<A>(parser: Parser<A>, str: string): Option<A>
  reads parser.run.reads;
  requires parser.run.requires(str);
  {
    var results := parser.run(str);
    if |results| == 0
    then Option.None
    else Option.Some(results[0].0)
  }

  method ParseFile<A>(parser: Parser<A>, filename: string) returns (res: Option<A>)
  requires forall s : string :: parser.run.requires(s)
  {
    var fname: array<char> := new char[|filename|];
    var contents: array<char> := Helpers.FileSystem.ReadFile(fname);
    if contents == null { return Option.None; }
    assert forall s : string :: parser.run.requires(s);
    var parseResult := Parse(parser, contents[..]);
    return parseResult;
  }

  /* default export Public { */
  /*   Parser, */
  /*   Const, */
  /*   SatChar, */
  /*   Or, */
  /*   Char, */
  /*   Digit, */
  /*   Letter, */
  /*   Then, */
  /*   Map, */
  /*   Skip, */
  /*   Seq, */
  /*   ZeroOrMore, */
  /*   OneOrMore, */
  /*   Parse, */
  /*   ParseFile */
  /* } */
}
