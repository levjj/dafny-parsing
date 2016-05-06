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

  function method Then<A,B>(pa: Parser<A>, pb: A -> Parser<B>): Parser<B>
  reads *;
  requires forall s:string :: pa.run.requires(s);
  requires forall a:A :: pb.requires(a);
  requires forall a:A, s:string :: pb(a).run.requires(s);
  ensures forall s:string :: Then(pa, pb).run.requires(s);
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
    var cont: A -> B -> Parser<C> := a
      reads * => b
      reads * => Const(f(a,b));
    var cont2: A -> Parser<C> := a
      reads * => Then<B,C>(pb, cont(a));
    Then<A,C>(pa, cont2)

    /* Then<A,C>(pa, */
    /* (a: A) reads pb.run.reads reads f.reads */
    /*        requires forall s:string :: pb.run.requires(s) */
    /*        requires forall b:B :: f.requires(a,b) */
    /*  => Then<B,C>(pb, */
    /* (b: B) reads f.reads requires f.requires(a,b) => Const(f(a,b)))) */
  }

  /* function method ZeroOrMoreP<A>(p: P<A>, limit: nat): P<seq<A>> */
  /* decreases limit */
  /* { */
  /*   var nothing: P<seq<A>> := ConstP([]); */
  /*   if limit == 0 */
  /*   then nothing */
  /*   else OrP(nothing, OneOrMoreP<A>(p, limit - 1)) */
  /* } */

  /* function method OneOrMoreP<A>(p: P<A>, limit: nat): P<seq<A>> */
  /* decreases limit */
  /* { */
  /*   ThenP<A,seq<A>>(p, (a: A) => */
  /*     if limit == 0 */
  /*     then ConstP([a]) */
  /*     else ThenP<seq<A>,seq<A>>(ZeroOrMoreP(p, limit - 1), (aa: seq<A>) => */
  /*          ConstP([a] + aa))) */
  /* } */

  /* method Or(parser2: Parser<A>) returns (p: Parser<A>) */
  /* requires parser2 != null */
  /* ensures p != null; */
  /* { */
  /*   return new Parser.P(Internal.OrP(parser, parser2.parser)); */
  /* } */

  /* method OneOrMore() returns (p: Parser<seq<A>>) */
  /* ensures p != null; */
  /* { */
  /*   return new Parser.P(Internal.ZeroOrMoreP(parser, 1000)); */
  /* } */

  /* method ZeroOrMore() returns (p: Parser<seq<A>>) */
  /* ensures p != null; */
  /* { */
  /*   return new Parser.P(Internal.OneOrMoreP(parser, 1000)); */
  /* } */

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

  default export Public {
    Parser,
    Const,
    SatChar,
    Or,
    Char,
    Digit,
    Letter,
    Parse
  }
}
