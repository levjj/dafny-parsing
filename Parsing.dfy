module Parsing {
  datatype Option<A> = Some(some: A) | None

  datatype Parser<A> = Parser(run: string -> Option<(A, string)>)

  class FileSystem {
    extern static method ReadFile(name:array<char>) returns (contents: array<char>)
  }

  function method Const<A>(a: A): Parser<A>
  ensures forall s:string :: Const(a).run.requires(s);
  {
    Parser(s => Some((a, s)))
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
                       => (var t: Option<(A,string)> := p.run(s);
                           if t.None?
                            then None
                            else Some((f(t.some.0), t.some.1))))
  }

  function method SatChar(pred: char -> bool): Parser<char>
  reads *;
  requires forall c:char :: pred.requires(c);
  ensures forall s:string :: SatChar(pred).run.requires(s);
  {
    Parser((s: string) reads *
                       requires |s| > 0 ==> pred.requires(s[0])
                       => if |s| == 0 then None
                          else if pred(s[0]) then Some((s[0], s[1..]))
                          else None)
  }

  function method Or<A>(p1: Parser<A>, p2: Parser<A>): Parser<A>
  reads *;
  requires forall s:string :: p1.run.requires(s);
  requires forall s:string :: p2.run.requires(s);
  ensures forall s:string :: Or(p1, p2).run.requires(s);
  {
    Parser((s: string) reads *
                       requires p1.run.requires(s) requires p2.run.requires(s)
                       => (var t: Option<(A,string)> := p1.run(s);
                           if t.Some?
                            then t
                            else p2.run(s)))
  }

  function method Char(c: char): Parser<char>
  reads *;
  ensures forall s:string :: Char(c).run.requires(s);
  {
    SatChar(c2 => c == c2)
  }

  function method Digit(): Parser<char>
  reads *;
  ensures forall s:string :: Digit().run.requires(s);
  {
    SatChar(c => '0' <= c <= '9')
  }

  function method Letter(): Parser<char>
  reads *;
  ensures forall s:string :: Letter().run.requires(s);
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
                  requires forall a: A, s: string :: pb(a).run.requires(s) => (
      var t: Option<(A,string)> := pa.run(s);
      if t.None? then None else pb(t.some.0).run(t.some.1)))
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

  function method SkipWS<A>(p: Parser<A>): Parser<A>
  reads *;
  requires forall s:string :: p.run.requires(s);
  ensures forall s:string :: SkipWS(p).run.requires(s);
  {
    var ws: Parser<string> := ZeroOrMore(Or(Or(Char(' '), Char('\t')), Char('\n')));
    Then(ws, Skip(p, ws))
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
    OneOrMoreLim(p, 100)
  }

  function method ZeroOrMore<A>(p: Parser<A>): Parser<seq<A>>
  reads *;
  requires forall s:string :: p.run.requires(s);
  ensures forall s:string :: ZeroOrMore(p).run.requires(s);
  {
    OneOrMoreLim(p, 100)
  }

  function method ZCombLim<A>(f: Parser<A> -> Parser<A>, limit: nat): Parser<A>
  decreases limit;
  reads *;
  requires f.requires(Parser(s => None));
  requires forall pa: Parser<A> :: f.requires(pa) ==> f.requires(f(pa));
  requires forall s:string, pa: Parser<A> :: f.requires(pa) && pa.run.requires(s) ==> f(pa).run.requires(s);
  ensures f.requires(ZCombLim(f, limit));
  ensures forall s:string :: ZCombLim(f, limit).run.requires(s);
  {
    if limit == 0
    then Parser(s => None)
    else f(ZCombLim(f, limit - 1))
  }

  function method ZComb<A>(f: Parser<A> -> Parser<A>): Parser<A>
  reads *;
  requires f.requires(Parser(s => None));
  requires forall pa: Parser<A> :: f.requires(pa) ==> f.requires(f(pa));
  requires forall s:string, pa: Parser<A> :: f.requires(pa) && pa.run.requires(s) ==> f(pa).run.requires(s);
  ensures f.requires(ZComb(f));
  ensures forall s:string :: ZComb(f).run.requires(s);
  {
    ZCombLim(f, 32)
  }

  function method Parse<A>(parser: Parser<A>, str: string): Option<A>
  reads *;
  requires forall s:string :: parser.run.requires(s);
  {
    var t: Option<(A, string)> := parser.run(str);
    if t.None? then None else if |t.some.1| > 0 then None else Some(t.some.0)
  }

  method ParseFile<A>(parser: Parser<A>, filename: string) returns (res: Option<A>)
  requires forall s : string :: parser.run.requires(s)
  {
    var fname: array<char> := new char[|filename|];
    var contents: array<char> := FileSystem.ReadFile(fname);
    if contents == null { return None; }
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
