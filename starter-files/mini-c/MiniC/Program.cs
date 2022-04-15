using System;
using _System;
using _module;
using Dafny;

namespace MiniC
{
  class Program
  {
    static void Main(string[] args) {
      if (args == null || args.Length != 2 || !(args[0] == "taint" || args[0] == "sectype")) {
        Console.WriteLine("Expected usage: main (taint|sectype) [filename.mc]");
        System.Environment.Exit(1);
      } else if (args[0] == "taint") {
        var filename = Sequence<char>.FromString(args[1]);
        __default.RunCommandTaintAnalysis(filename);
      } else {
        var filename = Sequence<char>.FromString(args[1]);
        __default.RunCommandSecTypes(filename);
      }
    }
  }
}