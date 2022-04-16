using System;
using System.Numerics;
using System.Collections.Generic;
using System.Linq;
using _System;
using Dafny;

namespace _module
{
  internal class AstBuilder : MiniCBaseVisitor<object>
  {
    public override object VisitProgram(MiniCParser.ProgramContext context) {
      var decls = VisitDeclarations(context.declarations());
      var ast = VisitBlock(context.block());

      return (decls, ast);
    }

    public override object VisitDecl(MiniCParser.DeclContext context) {
      var t_str = context.t.GetText();
      Type type = t_str == "bool" ? new Type_TBool() : new Type_TInt();
      var var = MakeVariable(context.v);
      var type_pair = new Dafny.Pair<Variable, Type>(var, type);
      var type_list = new List<Dafny.Pair<Variable, Type>>() {type_pair};

      var sec_type_list = new List<Dafny.Pair<Variable, SecType>>();
      if (context.s != null) {
        SecType sec_type = context.s.GetText() == "Low" ? new SecType_Low() : new SecType_High();
        sec_type_list.Add(new Dafny.Pair<Variable, SecType>(var, sec_type));
      }
      return (type_list, sec_type_list);
    }

    public override object VisitDeclarations(MiniCParser.DeclarationsContext context) {
      var type_list = new List<Dafny.Pair<Variable, Type>>();
      var sec_type_list = new List<Dafny.Pair<Variable, SecType>>();
      foreach (var decl in context.decl()) {
        var ret = (ValueTuple<List<Dafny.Pair<Variable, Type>>, List<Dafny.Pair<Variable, SecType>>>) VisitDecl(decl);
        type_list.AddRange(ret.Item1);
        sec_type_list.AddRange(ret.Item2);
      }
      return (type_list, sec_type_list);
    }

    private Variable MakeVariable(MiniCParser.IdContext id) {
      return new Variable(Sequence<char>.FromString(id.name.Text));
    }
    
    public override object VisitExp(MiniCParser.ExpContext context) {
      if (context.b != null) {
        if (context.b.val.Text == "True") {
          return Expr.create_Bool(true);
        } else {
          return Expr.create_Bool(false);
        }
      } else if (context.i != null) {
        BigInteger result = new BigInteger();
        BigInteger.TryParse(context.i.val.Text, out result);
        return Expr.create_Int(result);
      } else if (context.v != null) {
        return Expr.create_Var(MakeVariable(context.v));
      } else if (context.op != null) {
        Op o = null;
        if (context.op.Text == "+") {
          o = new Op_Plus();
        } else if (context.op.Text == "-") {
          o = new Op_Sub();
        } else if (context.op.Text == "*") {
          o = new Op_Times();
        } else if (context.op.Text == "<=") {
          o = new Op_Leq();
        } else if (context.op.Text == "==") {
          o = new Op_Eq();
        }
        return new Expr_BinaryOp(o, (Expr)VisitExp(context.left), (Expr)VisitExp(context.right));
      }
      
      // Unreachable
      return null;
    }

    public override object VisitBlock(MiniCParser.BlockContext context) {
      if (context.b != null) {
        var c = (Command) VisitCommand(context.lc);
        var rest = (Command) VisitBlock(context.b);
        return Command.create_Concat(c, rest);
      } else {
        return VisitCommand(context.c);
      }
    }

    public override object VisitCommand(MiniCParser.CommandContext context) {
      if (context.noopCommand() != null) {
        return VisitNoopCommand(context.noopCommand());
      } else if (context.assignCommand() != null) {
        return VisitAssignCommand(context.assignCommand());
      } else if (context.ifCommand() != null) {
        return VisitIfCommand(context.ifCommand());
      } else if (context.whileCommand() != null) {
        return VisitWhileCommand(context.whileCommand());
      } else if (context.printSCommand() != null) {
        return VisitPrintSCommand(context.printSCommand());
      } else if (context.printECommand() != null) {
        return VisitPrintECommand(context.printECommand());
      } else if (context.getIntCommand() != null) {
        return VisitGetIntCommand(context.getIntCommand());
      } else if (context.getSecretIntCommand() != null) {
        return VisitGetSecretIntCommand(context.getSecretIntCommand());
      }

      // Unreachable
      return null;
    }
    
    public override object VisitNoopCommand(MiniCParser.NoopCommandContext context) {
      return Command.create_Noop();
    }

    public override object VisitAssignCommand(MiniCParser.AssignCommandContext context) {
      return Command.create_Assign(MakeVariable(context.v), (Expr) VisitExp(context.e));
    }

    public override object VisitIfCommand(MiniCParser.IfCommandContext context) {
      return Command.create_IfThenElse((Expr) VisitExp(context.cond), (Command) VisitBlock(context.ifTrue),
        (Command) VisitBlock(context.ifFalse));
    }

    public override object VisitWhileCommand(MiniCParser.WhileCommandContext context) {
      return Command.create_While((Expr) VisitExp(context.cond), (Command) VisitBlock(context.body));
    }

    public override object VisitPrintSCommand(MiniCParser.PrintSCommandContext context) {
      return Command.create_PrintS(Sequence<char>.FromString(context.s.Text.Trim('\'')));
    }

    public override object VisitPrintECommand(MiniCParser.PrintECommandContext context) {
      return Command.create_PrintE((Expr) VisitExp(context.e));
    }

    public override object VisitGetIntCommand(MiniCParser.GetIntCommandContext context) {
      return Command.create_GetInt(Variable.create(Sequence<char>.FromString(context.v.name.Text)));
    }

    public override object VisitGetSecretIntCommand(MiniCParser.GetSecretIntCommandContext context) {
      return Command.create_GetSecretInt(Variable.create(Sequence<char>.FromString(context.v.name.Text)));
    }
  }
  
  
  public partial class __default
  {
    
  }
  

}
