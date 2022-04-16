using System;
using System.Numerics;
using System.IO;
using System.Collections.Generic;
using _System;
using Dafny;
using Antlr4.Runtime;

namespace _module
{
  public partial class __default
  {
    public static void ParseFileNormal(ISequence<char> filename, out Dafny.IMap<_IVariable, _IType> decls, out _ICommand ast) {
      string text = System.IO.File.ReadAllText(Dafny.Helpers.ToString(filename));
      var inputStream = new AntlrInputStream(new StringReader(text));
      var lexer = new MiniCLexer(inputStream);
      var tokenStream = new CommonTokenStream(lexer);
      var parser = new MiniCParser(tokenStream);

      try {
        var parse_tree = parser.program();
        var ast_builder = new AstBuilder();
        var result = (ValueTuple<object, object>) ast_builder.VisitProgram(parse_tree);
        var decls_pair = (ValueTuple<List<Dafny.Pair<Variable, _module.Type>>,List<Dafny.Pair<Variable, _module.SecType>>>)result.Item1;
        var type_list = (List<Dafny.Pair<Variable, _module.Type>>) decls_pair.Item1;
        ast = (Command) result.Item2;
        decls = Map<Variable, _module.Type>.FromCollection(type_list);
      }  catch (Exception e) {
        Console.WriteLine(e.Message);
        decls = null;
        ast = null;
        System.Environment.Exit(5);
      }
    }
    
    public static void ParseFileSecTypes(ISequence<char> filename, out Dafny.IMap<_IVariable, _ISecType> decls, out _ICommand ast) {
      string text = System.IO.File.ReadAllText(Dafny.Helpers.ToString(filename));
      var inputStream = new AntlrInputStream(new StringReader(text));
      var lexer = new MiniCLexer(inputStream);
      var tokenStream = new CommonTokenStream(lexer);
      var parser = new MiniCParser(tokenStream);

      try {
        var parse_tree = parser.program();
        var ast_builder = new AstBuilder();
        var result = (ValueTuple<object, object>) ast_builder.VisitProgram(parse_tree);
        var decls_pair = (ValueTuple<List<Dafny.Pair<Variable, _module.Type>>,List<Dafny.Pair<Variable, _module.SecType>>>)result.Item1;
        var type_list = (List<Dafny.Pair<Variable, _module.SecType>>) decls_pair.Item2;
        ast = (Command) result.Item2;
        decls = Map<Variable, _module.SecType>.FromCollection(type_list);
      }  catch (Exception e) {
        Console.WriteLine(e.Message);
        decls = null;
        ast = null;
        System.Environment.Exit(5);
      }
    }
    
    public static IO PrintString(Dafny.ISequence<char> s) {
      Dafny.Helpers.Print(s);
      return new IO();
    }

    public static Dafny.ISequence<char> Int2String(BigInteger i) {
      return Dafny.Sequence<char>.FromString(i.ToString());
    }

    public static _System.Tuple2<BigInteger, IO> ReadInt() {
      while (true) {
        Console.WriteLine("Public input: ");
        string val = Console.ReadLine();
        BigInteger result = new BigInteger();
        var b = BigInteger.TryParse(val, out result);
        if (b) {
          return new Tuple2<BigInteger, IO>(result, new IO());
        }
        else {
          Console.WriteLine("Invalid integer!  Try again.");
        }
      }
    }

    public static _System.Tuple2<BigInteger, IO> ReadSecretInt() {
      while (true) {
        Console.WriteLine("Secret input: ");
        string val = Console.ReadLine();
        BigInteger result = new BigInteger();
        var b = BigInteger.TryParse(val, out result);
        if (b) {
          return new Tuple2<BigInteger, IO>(result, new IO());
        }
        else {
          Console.WriteLine("Invalid integer!  Try again.");
        }
      }
    }
  }
}
