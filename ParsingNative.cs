using System;
using System.IO;
using Dafny;

namespace @_0_Parsing_Compile {
  public partial class Option<A> {
    private readonly A val;
    private readonly bool isNone;
    public Option(A a) {
      this.val = a;
      this.isNone = false;
    }
    public Option() {
      this.isNone = true;
    }
    public bool IsNone() { return isNone; }
    public A Val() { return val; }
    public override string ToString() {
      if (isNone) {
        return "None";
      } else {
        return "Some(" + val.ToString() + ")";
      }
    }
  }

  public partial class Parser<A> {
    internal readonly Func<string, Tuple<A, string>> p;

    internal Parser(Func<string, Tuple<A, string>> p) {
      this.p = p;
    }

    public Parser<B> Map<B>(Func<A, B> f) {
      return new Parser<B>(s => {
        Tuple<A, string> t = p(s);
        return t == null ? null : Tuple.Create(f(t.Item1), t.Item2);
      });
    }

    public Parser<A> Or(Parser<A> p2) {
      return new Parser<A>(s => {
        Tuple<A, string> r = p(s);
        return r == null ? p2.p(s): r;
      });
    }

    public Parser<B> Bind<B>(Func<A, Parser<B>> f) {
      return new Parser<B>(s => {
        Tuple<A, string> r = p(s);
        if (r == null) return null;
        Parser<B> pb = f(r.Item1);
        return pb.p(r.Item2);
      });
    }

    public Parser<C> Seq<B,C>(Parser<B> pb, Func<A, B, C> f) {
      return Bind(a => {
        return pb.Bind(b => @_0_Parsing_Compile.Parse.Const(f(a,b)));
      });
    }

    public Parser<A> Skip<B>(Parser<B> pb) {
      return Seq(pb, (a,b) => a);
    }

    public Parser<B> Then<B>(Parser<B> pb) {
      return Seq(pb, (a,b) => b);
    }

    public Parser<A> SkipWS() {
      Parser<Sequence<char>> ws = @_0_Parsing_Compile.Parse.Char(' ')
        .Or(@_0_Parsing_Compile.Parse.Char('\t'))
        .Or(@_0_Parsing_Compile.Parse.Char('\n')).ZeroOrMore();
      return ws.Then(Skip(ws));
    }

    public Parser<Sequence<A>> ZeroOrMore() {
      return OneOrMore().Or(@_0_Parsing_Compile.Parse.Const(Sequence<A>.Empty));
    }

    public Parser<Sequence<A>> OneOrMore() {
      return Bind<Sequence<A>>(a =>
        ZeroOrMore().Bind<Sequence<A>>(aa =>
          @_0_Parsing_Compile.Parse.Const(
            Sequence<A>.FromElements(a).Concat(aa))));
    }

    private Option<A> Parse(string str) {
      Tuple<A, string> t = p(str.ToString());
      return t == null || !string.IsNullOrEmpty(t.Item2)
        ? new Option<A>()
          : new Option<A>(t.Item1);
    }

    public Option<A> Parse(Sequence<char> str) {
      return Parse(str.ToString());
    }

    public Option<A> ParseFile(Sequence<char> filename) {
      string sname = filename.ToString();
      return Parse(File.ReadAllText(sname));
    }
  }

  public partial class Parse {
    public static Parser<A> Const<A>(A a) {
      return new Parser<A>(s => Tuple.Create(a, s));
    }

    public static Parser<char> SatChar(Func<char, bool> pred) {
      return new Parser<char>(s => {
        if (s.Length == 0) {
          return null;
        } else if (pred(s[0])) {
          return Tuple.Create(s[0], s.Substring(1));
        } else {
          return null;
        }
      });
    }

    public static Parser<char> Char(char c2) {
      return SatChar(c => c == c2);
    }

    public static Parser<char> Digit() {
      return SatChar(c => '0' <= c && c <= '9');
    }

    public static Parser<char> Letter() {
      return SatChar(c => 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z' || c == '_');
    }

    /*public static Parser<string> Keyword(string kw) {
      
    }*/

    public static Parser<A> Fix<A>(Func<Parser<A>, Parser<A>> f) {
      return new Parser<A>(s => f(Fix(f)).p(s));
    }
  }
}