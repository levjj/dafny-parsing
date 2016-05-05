module Parsing {
  datatype Option<A> = Some(some: A) | None
  datatype Parser<A> = Parser(run: string -> seq<(A, string)>)

  function method SatP(pred: char -> bool): Parser<char>
  {
    Parser((s: string) reads pred.reads requires |s| > 0 ==> pred.requires(s[0])
                       => if |s| == 0 then []
                          else if pred(s[0]) then [(s[0], s[1..])]
                          else [])
  }

  function method DigitP(): Parser<char>
  {
    SatP(c => '0' <= c <= '9')
  }

  function method LetterP(): Parser<char>
  {
    SatP(c => 'A' <= c <= 'Z' || 'a' <= c <= 'z' || c == '_')
  }

  function method OrP<A>(p1: Parser<A>, p2: Parser<A>): Parser<A>
  {
    Parser((s: string) reads p1.run.reads reads p2.run.reads
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

  function method ThenP<A,B>(pa: Parser<A>, pb: A -> Parser<B>): Parser<B>
  reads *
  {
    Parser((s: string) reads *
                       requires pa.run.requires(s)
                       requires forall x: A :: pb.requires(x)
                       requires forall a: A, s: string :: pb(a).run.requires(s) =>
    (
      var par: seq<(A, string)> := pa.run(s);
      var pcomb: seq<seq<(B, string)>> := Map(par, (a_s: (A, string))
                       reads *
                       requires forall x: A :: pb.requires(x)
                       requires forall a: A, s: string :: pb(a).run.requires(s)
                       => pb(a_s.0).run(a_s.1));
      Flatten(pcomb)
    ))
  }

  class FileSystem {
    extern static method ReadFile(name:array<char>) returns (contents: array<char>)
  }

  function method Parse<A>(parser: Parser<A>, str: string): Option<A>
  reads parser.run.reads;
  requires forall s : string :: parser.run.requires(s);
  {
    var results: seq<(A, string)> := parser.run(str);
    if |results| == 0 then None else Some(results[0].0)
  }

  method ParseFile<A>(parser: Parser<A>, filename: string) returns (res: Option<A>)
  requires forall s : string :: parser.run.requires(s)
  {
    var fname: array<char> := new char[|filename|];
    var contents: array<char> := FileSystem.ReadFile(fname);
    if contents == null { return None; }
    var parseResult := Parse(parser, contents[..]);
    return parseResult;
  }
}
