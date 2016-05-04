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

  /*function method ThenP<A,B>(p1: Parser<A>, p2: Parser<B>): Parser<A>
  {
    p1
  }*/

  function method OrP<A>(p1: Parser<A>, p2: Parser<A>): Parser<A>
  {
    p1
  }

  /*function method ManyP(p: Parser<A>): Parser<seq<A>>
  {
    Parser((s: string) reads pred.reads requires |s| > 0 ==> pred.requires(s[0])
                       => if |s| == 0 then []
                          else if pred(s[0]) then [(s[0], s[1..])]
                          else [])
  }*/

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
