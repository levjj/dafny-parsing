module Parsing {
  module Internal {
    datatype Option<A> = Some(some: A) | None
    datatype P<A> = P(run: string -> seq<(A, string)>)

    function method SatP(pred: char -> bool): P<char>
    reads pred.reads;
    requires forall c:char :: pred.requires(c);
    ensures forall s:string :: SatP(pred).run.requires(s);
    {
      P((s: string) reads pred.reads requires forall c:char :: pred.requires(c)
                        => if |s| == 0 then []
                            else if pred(s[0]) then [(s[0], s[1..])]
                            else [])
    }

    function method OrP<A>(p1: P<A>, p2: P<A>): P<A>
    reads p1.run.reads;
    reads p2.run.reads;
    requires forall s:string :: p1.run.requires(s);
    requires forall s:string :: p2.run.requires(s);
    ensures forall s:string :: OrP(p1, p2).run.requires(s);
    {
      P((s: string) reads p1.run.reads reads p2.run.reads
                    requires p1.run.requires(s) requires p2.run.requires(s)
                    => p1.run(s) + p2.run(s))
    }

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

    function method ConstP<A>(a: A): P<A>
    ensures forall s:string :: ConstP(a).run.requires(s) && ConstP(a).run.reads(s) == {};
    {
      P((s: string)  => [(a, s)])
    }

    /* function method ThenP<A,B>(pa: P<A>, pb: A -> P<B>): P<B> */
    /* reads pa.run.reads; */
    /* reads pb.reads; */
    /* requires forall s:string :: pa.run.requires(s); */
    /* requires forall a:A, s:string :: pb(a).run.requires(s); */
    /* ensures forall s:string :: ThenP(pa, pb).run.requires(s); */
    /* { */
    /*   P((s: string) reads * */
    /*                 requires pa.run.requires(s) */
    /*                 requires forall x: A :: pb.requires(x) */
    /*                 requires forall a: A, s: string :: pb(a).run.requires(s) => */
    /*   ( */
    /*     var par: seq<(A, string)> := pa.run(s); */
    /*     var pcomb: seq<seq<(B, string)>> := Map(par, (a_s: (A, string)) */
    /*                     reads * */
    /*                     requires forall x: A :: pb.requires(x) */
    /*                     requires forall a: A, s: string :: pb(a).run.requires(s) */
    /*                     => pb(a_s.0).run(a_s.1)); */
    /*     Flatten(pcomb) */
    /*   )) */
    /* } */

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

    class FileSystem {
      extern static method ReadFile(name:array<char>) returns (contents: array<char>)
    }
  }

  class Parser<A> {
    var parser: Internal.P<A>;

    constructor (a: A) modifies this
    requires forall p: Parser<A>, s:string :: p != null ==> p.parser.run.requires(s) && !(this in p.parser.run.reads(s));
    ensures forall p: Parser<A>, s:string :: p != null ==> p.parser.run.requires(s) && !(this in p.parser.run.reads(s));
    {
      parser := Internal.ConstP(a);
    }

    constructor P(p: Internal.P<A>) modifies this
    requires forall s:string :: !(this in p.run.reads(s));
    requires forall s:string :: p.run.requires(s);
    ensures forall s:string :: parser.run.requires(s);
    {
      parser := p;
    }

    static method Char(c: char) returns (p: Parser<char>)
    ensures p != null;
    {
      return new Parser<char>.P(Internal.SatP(c2 => c == c2));
    }

    static method Digit() returns (p: Parser<char>)
    ensures p != null;
    ensures forall s:string :: p.parser.run.requires(s);
    {
      return new Parser<char>.P(Internal.SatP(c => '0' <= c <= '9'));
    }

    static method Letter() returns (p: Parser<char>)
    ensures p != null;
    ensures forall s:string :: p.parser.run.requires(s);
    {
      return new Parser<char>.P(Internal.SatP(c => 'A' <= c <= 'Z' || 'a' <= c <= 'z' || c == '_'));
    }

    /* method Then<B,C>(pb: Parser<B>, f: (A,B) -> C) returns (p: Parser<C>) */
    /* requires pb != null */
    /* ensures p != null; */
    /* { */
    /*   return new Parser<C>.P(Internal.ThenP(parser, */
    /*     (a: A) reads pb => Internal.ThenP<B,C>(pb.parser, */
    /*     (b: B) reads f.reads requires f.requires(a,b) => Internal.ConstP(f(a,b))))); */
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

    function method Parse(str: string): Internal.Option<A>
    reads this
    reads parser.run.reads;
    requires parser.run.requires(str);
    {
      var results := parser.run(str);
      if |results| == 0
      then Internal.Option.None
      else Internal.Option.Some(results[0].0)
    }

    /* method ParseFile(filename: string) returns (res: Internal.Option<A>) */
    /* requires forall s : string :: parser.run.requires(s) */
    /* { */
    /*   var fname: array<char> := new char[|filename|]; */
    /*   var contents: array<char> := Internal.FileSystem.ReadFile(fname); */
    /*   if contents == null { return Internal.Option.None; } */
    /*   assert forall s : string :: parser.run.requires(s); */
    /*   var parseResult := Parse(contents[..]); */
    /*   return parseResult; */
    /* } */
  }
}

