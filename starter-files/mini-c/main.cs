// Dafny program main.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.5.0.40314
// Command Line Options: /compile:0 /spillTargetCode:3 main.dfy
// main.dfy

method {:extern} ParseFileNormal(filename: string) returns (d: Declarations, c: Command)
  decreases filename

method {:extern} ParseFileSecTypes(filename: string) returns (d: SecDeclarations, c: Command)
  decreases filename

method RunCommandTaintAnalysis(filename: string, ghost io: IO)
  decreases filename, io
{
  var decls, cmd := ParseFileNormal(filename);
  if !CommandWellTyped(decls, cmd) {
    print ""Sorry, the command is not well typed.\n"";
  } else {
    var store := map v: Variable {:trigger decls[v]} {:trigger v in decls} | v in decls :: if decls[v].TBool? then B(false) else I(0);
    var vars_map := map v: Variable {:trigger v in decls} | v in decls :: false;
    var taint_state := TaintState(4294967295, store, io, false, vars_map);
    var result := EvalCommandTaint(decls, taint_state, cmd);
    match result {
      case {:split false} TTimeout() =>
        print ""\nExecution timed out.  You probably have an infinite loop in your code.\n"";
      case {:split false} TLeak() =>
        print ""\nYour program tried to leak a secret, but we caught you!\n"";
      case {:split false} TSuccess(_) =>
        print ""\nCongratulations, your program ran to completion.\n"";
    }
  }
}

method RunCommandSecTypes(filename: string, ghost io: IO)
  decreases filename, io
{
  var decls, cmd := ParseFileSecTypes(filename);
  if CommandHasSecType(decls, cmd, Low) {
    print ""Command is well typed at Low\n"";
  } else if CommandHasSecType(decls, cmd, High) {
    print ""Command is well typed at High\n"";
  } else {
    print ""Sorry, the command is not well typed.\n"";
    return;
  }
  var store := map v: Variable {:trigger v in decls} | v in decls :: B(false);
  var state := State(4294967295, store, io);
  var result := EvalCommand(state, cmd);
  match result {
    case {:split false} Timeout() =>
      print ""\nExecution timed out.  You probably have an infinite loop in your code.\n"";
    case {:split false} Fail() =>
      print ""\nSorry, your program failed during execution.\n"";
    case {:split false} Success(_, _) =>
      print ""\nCongratulations, your program ran to completion.\n"";
  }
}

function ToState(s: TaintState): State
  decreases s
{
  State(s.fuel, s.store, s.io)
}

predicate AllVariablesTracked(s: TaintState)
  decreases s
{
  forall v: Variable :: 
    v in s.store ==>
      v in s.var_map
}

function method EvalExprTaint(d: Declarations, s: TaintState, e: Expr, t: Type): (tv: TaintValue)
  requires ExprHasType(d, e, t)
  requires StoreWellTyped(d, s.store)
  requires AllVariablesTracked(s)
  ensures EvalExpr(e, s.store).ESuccess?
  ensures tv.v == EvalExpr(e, s.store).v
  decreases d, s, e, t
{
  WellTypedExprSuccess(d, s.store, e, t);
  match e
  case Bool(b) =>
    TV(false, B(b))
  case Int(i) =>
    TV(false, I(i))
  case Var(v) =>
    TV(s.var_map[v], s.store[v])
  case BinaryOp(op, lhs, rhs) =>
    var lhs := EvalExprTaint(d, s, lhs, TInt);
    var rhs := EvalExprTaint(d, s, rhs, TInt);
    if lhs.tainted == true || rhs.tainted == true then
      match op
      case Plus =>
        TV(true, I(lhs.v.i + rhs.v.i))
      case Sub =>
        TV(true, I(lhs.v.i - rhs.v.i))
      case Times =>
        if (lhs.tainted == false && lhs.v == I(0)) || (rhs.tainted == false && rhs.v == I(0)) then
          TV(false, I(0))
        else
          TV(true, I(lhs.v.i * rhs.v.i))
      case Leq =>
        TV(true, B(lhs.v.i <= rhs.v.i))
      case Eq =>
        TV(true, B(lhs.v.i == rhs.v.i))
    else
      match op case Plus => TV(false, I(lhs.v.i + rhs.v.i)) case Sub => TV(false, I(lhs.v.i - rhs.v.i)) case Times => TV(false, I(lhs.v.i * rhs.v.i)) case Leq => TV(false, B(lhs.v.i <= rhs.v.i)) case Eq => TV(false, B(lhs.v.i == rhs.v.i))
}

lemma TaintExamplesExpr(io: IO)
  decreases io
{
}

function method UpdateVarTaint(s: TaintState, v: Variable, taint: bool): TaintState
  decreases s, v, taint
{
  s.(var_map := s.var_map[v := taint])
}

function method UpdateVarVal(s: TaintState, v: Variable, val: Value): TaintState
  decreases s, v, val
{
  s.(store := s.store[v := val])
}

function method UpdatePCTaint(s: TaintState, taint: bool): TaintState
  decreases s, taint
{
  s.(pc_tainted := taint)
}

function method {:extern} PrintErr(s: string): ()
  decreases s

function method EvalCommandTaint(d: Declarations, s: TaintState, c: Command): (t: TResult)
  requires CommandWellTyped(d, c)
  requires StoreWellTyped(d, s.store)
  requires AllVariablesTracked(s)
  ensures t.TSuccess? ==> AllVariablesTracked(t.s) && StoreWellTyped(d, t.s.store) && t.s.fuel <= s.fuel
  ensures var r: CResult := EvalCommand(ToState(s), c); t.TSuccess? ==> r.Success? && r.s == t.s.store && r.io == t.s.io
  decreases s.fuel, c
{
  WellTypedCommandSuccess(d, ToState(s), c);
  if s.fuel == 0 then
    TTimeout
  else
    match c { case Noop => TSuccess(s) case Assign(_mcc#0: Variable, _mcc#1: Expr) => (var e := _mcc#1; var variable := _mcc#0; if !s.var_map[variable] && s.pc_tainted then TLeak else var TV(taint, value) := EvalExprTaint(d, s, e, d[variable]); var new_taint := taint || s.pc_tainted; var new_s := UpdateVarTaint(s, variable, new_taint); var s' := UpdateVarVal(new_s, variable, value); TSuccess(s')) case Concat(_mcc#2: Command, _mcc#3: Command) => (var c1 := _mcc#3; var c0 := _mcc#2; var result0 := EvalCommandTaint(d, s, c0); match result0 case TTimeout => TTimeout case TLeak => TLeak case TSuccess(s') => WellTypedCommandSuccess(d, ToState(s), c0); EvalCommandTaint(d, s'.(fuel := s.fuel), c1)) case IfThenElse(_mcc#4: Expr, _mcc#5: Command, _mcc#6: Command) => (var ifFalse := _mcc#6; var ifTrue := _mcc#5; var cond := _mcc#4; var TV(taint, B(b)) := EvalExprTaint(d, s, cond, TBool); if b then var new_s := if taint then UpdatePCTaint(s, true) else s; var result := EvalCommandTaint(d, new_s, ifTrue); match result case TTimeout => TTimeout case TLeak => TLeak case TSuccess(s') => TSuccess(UpdatePCTaint(s', s.pc_tainted)) else var new_s := if taint then UpdatePCTaint(s, true) else s; var result := EvalCommandTaint(d, new_s, ifFalse); match result case TTimeout => TTimeout case TLeak => TLeak case TSuccess(s') => TSuccess(UpdatePCTaint(s', s.pc_tainted))) case While(_mcc#7: Expr, _mcc#8: Command) => (var body := _mcc#8; var cond := _mcc#7; var TV(taint, B(b)) := EvalExprTaint(d, s, cond, TBool); if !b then TSuccess(s) else var new_s := if taint then UpdatePCTaint(s, true) else s; var result := EvalCommandTaint(d, new_s.(fuel := s.fuel - 1), Concat(body, c)); match result case TTimeout => TTimeout case TLeak => TLeak case TSuccess(s') => TSuccess(UpdatePCTaint(s', s.pc_tainted))) case PrintS(_mcc#9: string) => (var str := _mcc#9; if s.pc_tainted then TLeak else var io' := PrintString(str, s.io); TSuccess(s.(io := io'))) case PrintE(_mcc#10: Expr) => (var e := _mcc#10; if s.pc_tainted then TLeak else var value := EvalExpr(e, s.store); match value case EFail => TSuccess(s) case ESuccess(I(i)) => (var TV(taint, value) := EvalExprTaint(d, s, e, TInt); var str := Int2String(i); var io' := PrintString(str, s.io); var s' := s.(io := io'); if taint then TLeak else TSuccess(s')) case ESuccess(B(b)) => var TV(taint, B(b)) := EvalExprTaint(d, s, e, TBool); var str := Bool2String(b); var io' := PrintString(str, s.io); var s' := s.(io := io'); if taint then TLeak else TSuccess(s')) case GetInt(_mcc#11: Variable) => (var variable := _mcc#11; if s.pc_tainted then TLeak else var (i, io') := ReadInt(s.io.(in_secret := [])); var new_store := s.store[variable := I(i)]; var new_s := UpdateVarTaint(s, variable, false); TSuccess(TaintState(s.fuel, new_store, io'.(in_secret := s.io.in_secret), new_s.pc_tainted, new_s.var_map))) case GetSecretInt(_mcc#12: Variable) => var variable := _mcc#12; if !s.var_map[variable] && s.pc_tainted then TLeak else var (i, io') := ReadSecretInt(s.io); var new_store := s.store[variable := I(i)]; var new_s := UpdateVarTaint(s, variable, true); TSuccess(TaintState(s.fuel, new_store, io', new_s.pc_tainted, new_s.var_map)) }
}

lemma TaintExamplesCommand(io: IO)
  decreases io
{
}

predicate UntaintedVarsAgree(d: Declarations, s0: TaintState, s1: TaintState)
  requires AllVariablesTracked(s0) && AllVariablesTracked(s1)
  decreases d, s0, s1
{
  forall variable: Variable :: 
    variable in d ==>
      variable in s0.store &&
      variable in s1.store &&
      (s0.var_map[variable] <==> s1.var_map[variable]) &&
      (!s0.var_map[variable] ==>
        s0.store[variable] == s1.store[variable])
}

lemma /*{:_induction d, s0, s1, e, t}*/ NonInterfenceExpr(d: Declarations, s0: TaintState, s1: TaintState, e: Expr, t: Type)
  requires ExprHasType(d, e, t)
  requires StoreWellTyped(d, s0.store) && StoreWellTyped(d, s1.store)
  requires AllVariablesTracked(s0) && AllVariablesTracked(s1)
  requires UntaintedVarsAgree(d, s0, s1)
  ensures EvalExprTaint(d, s0, e, t).tainted <==> EvalExprTaint(d, s1, e, t).tainted
  ensures !EvalExprTaint(d, s0, e, t).tainted ==> EvalExprTaint(d, s0, e, t).v == EvalExprTaint(d, s1, e, t).v
  decreases d, s0, s1, e, t
{
}

lemma /*{:_induction d, s, c}*/ TaintedPcPreservesLowVarsPubIO(d: Declarations, s: TaintState, c: Command, r: TResult)
  requires CommandWellTyped(d, c) && StoreWellTyped(d, s.store)
  requires AllVariablesTracked(s)
  requires s.pc_tainted
  requires EvalCommandTaint(d, s, c) == r
  requires r.TSuccess?
  ensures AllVariablesTracked(r.s)
  ensures UntaintedVarsAgree(d, s, r.s)
  ensures r.s.pc_tainted
  ensures r.s.io.in_public == s.io.in_public
  ensures r.s.io.output == s.io.output
  decreases s.fuel, c
{
}

lemma /*{:_induction d, s0, s1, c}*/ NonInterferenceInternal(d: Declarations, s0: TaintState, s1: TaintState, c: Command, r0: TResult, r1: TResult)
  requires CommandWellTyped(d, c) && StoreWellTyped(d, s0.store) && StoreWellTyped(d, s1.store)
  requires AllVariablesTracked(s0) && AllVariablesTracked(s1)
  requires s0.io.in_public == s1.io.in_public && s0.io.output == s1.io.output
  requires UntaintedVarsAgree(d, s0, s1)
  requires s0.pc_tainted == s1.pc_tainted
  requires EvalCommandTaint(d, s0, c) == r0
  requires EvalCommandTaint(d, s1, c) == r1
  requires r0.TSuccess?
  requires r1.TSuccess?
  ensures StoreWellTyped(d, r0.s.store) && StoreWellTyped(d, r1.s.store)
  ensures AllVariablesTracked(r0.s) && AllVariablesTracked(r1.s)
  ensures UntaintedVarsAgree(d, r0.s, r1.s)
  ensures r0.s.pc_tainted == r1.s.pc_tainted
  ensures r0.s.io.in_public == r1.s.io.in_public
  ensures r0.s.io.output == r1.s.io.output
  decreases s0.fuel, s1.fuel, c
{
}

lemma /*{:_induction d, s0, s1, c}*/ NonInterference(d: Declarations, s0: TaintState, s1: TaintState, c: Command, r0: TResult, r1: TResult)
  requires CommandWellTyped(d, c) && StoreWellTyped(d, s0.store) && StoreWellTyped(d, s1.store)
  requires AllVariablesTracked(s0) && AllVariablesTracked(s1)
  requires s0.io.in_public == s1.io.in_public && s0.io.output == s1.io.output
  requires UntaintedVarsAgree(d, s0, s1)
  requires s0.pc_tainted == s1.pc_tainted
  requires EvalCommandTaint(d, s0, c) == r0
  requires EvalCommandTaint(d, s1, c) == r1
  requires r0.TSuccess?
  requires r1.TSuccess?
  ensures r0.s.io.output == r1.s.io.output
  decreases d, s0, s1, c, r0, r1
{
}

predicate leq(t0: SecType, t1: SecType)
  decreases t0, t1
{
  t0 == t1 || (t0.Low? && t1.High?)
}

predicate method ExprHasSecType(d: SecDeclarations, e: Expr, t: SecType)
  decreases d, e, t
{
  match e
  case Bool(_) =>
    true
  case Int(_) =>
    true
  case Var(v) =>
    if v in d then
      d[v] == t
    else
      false
  case BinaryOp(op, left, right) =>
    ExprHasSecType(d, left, t) &&
    ExprHasSecType(d, right, t)
}

predicate method CommandHasSecTypeBasic(d: SecDeclarations, c: Command, t: SecType)
  decreases c, 0
{
  match c
  case Noop() =>
    true
  case Assign(variable, e) =>
    if variable in d then
      d[variable] == t &&
      ExprHasSecType(d, e, t)
    else
      false
  case Concat(c0, c1) =>
    CommandHasSecType(d, c0, t) &&
    CommandHasSecType(d, c1, t)
  case IfThenElse(cond, ifTrue, ifFalse) =>
    ExprHasSecType(d, cond, t) &&
    CommandHasSecType(d, ifTrue, t) &&
    CommandHasSecType(d, ifFalse, t)
  case While(cond, body) =>
    ExprHasSecType(d, cond, t) &&
    CommandHasSecType(d, body, t)
  case PrintS(str) =>
    if t == Low then
      true
    else
      false
  case PrintE(e) =>
    ExprHasSecType(d, e, Low) &&
    t == Low
  case GetInt(variable) =>
    ExprHasSecType(d, Var(variable), Low) &&
    t == Low
  case GetSecretInt(variable) =>
    ExprHasSecType(d, Var(variable), High) &&
    t == High
}

predicate method CommandHasSecType(d: SecDeclarations, c: Command, t: SecType)
  decreases c, 1
{
  CommandHasSecTypeBasic(d, c, t) || (t.Low? && CommandHasSecTypeBasic(d, c, High))
}

lemma NIexamples()
{
}

predicate VarsAgree(d: SecDeclarations, t: SecType, s0: Store, s1: Store)
  decreases d, t, s0, s1
{
  forall variable: Variable :: 
    variable in d ==>
      variable in s0 &&
      variable in s1 &&
      (d[variable] == t ==>
        s0[variable] == s1[variable])
}

function DecrFuel(s: State): State
  requires s.fuel > 0
  decreases s
{
  s.(fuel := s.fuel - 1)
}

lemma /*{:_induction d, s0, s1, e, t}*/ NonInterfenceTypeExpr(d: SecDeclarations, s0: Store, s1: Store, e: Expr, t: SecType)
  requires EvalExpr(e, s0).ESuccess?
  requires EvalExpr(e, s1).ESuccess?
  requires ExprHasSecType(d, e, t)
  requires VarsAgree(d, t, s0, s1)
  ensures EvalExpr(e, s0) == EvalExpr(e, s1)
  decreases d, s0, s1, e, t
{
}

lemma /*{:_induction d, c, s}*/ HighCommandPreservesLowVars(d: SecDeclarations, c: Command, s: State, store': Store)
  requires EvalCommand(s, c).Success? && EvalCommand(s, c).s == store'
  requires CommandHasSecType(d, c, High)
  ensures forall v: Variable :: v in s.store.Keys ==> v in store'.Keys && (v in d && d[v].Low? ==> store'[v] == s.store[v])
  decreases s.fuel, c
{
}

lemma /*{:_induction d, c, s}*/ HighCommandPreservesPubIO(d: SecDeclarations, c: Command, s: State, r: CResult)
  requires EvalCommand(s, c) == r && r.Success?
  requires CommandHasSecType(d, c, High)
  ensures r.io.in_public == s.io.in_public
  ensures r.io.output == s.io.output
  decreases s.fuel, c
{
}

lemma /*{:_induction d, c, t, s0, s1}*/ NonInterferenceTypesInternal(d: SecDeclarations, c: Command, t: SecType, s0: State, s1: State, r0: CResult, r1: CResult)
  requires EvalCommand(s0, c) == r0
  requires EvalCommand(s1, c) == r1
  requires r0.Success?
  requires r1.Success?
  requires s0.io.in_public == s1.io.in_public && s0.io.output == s1.io.output
  requires CommandHasSecType(d, c, t)
  requires VarsAgree(d, Low, s0.store, s1.store)
  ensures VarsAgree(d, Low, r0.s, r1.s)
  ensures r0.io.in_public == r1.io.in_public
  ensures r0.io.output == r1.io.output
  decreases s0.fuel, s1.fuel, c
{
}

lemma /*{:_induction d, c, t, s0, s1}*/ NonInterferenceTypes(d: SecDeclarations, c: Command, t: SecType, s0: State, s1: State, r0: CResult, r1: CResult)
  requires EvalCommand(s0, c) == r0
  requires EvalCommand(s1, c) == r1
  requires r0.Success?
  requires r1.Success?
  requires CommandHasSecType(d, c, t)
  requires VarsAgree(d, Low, s0.store, s1.store)
  requires s0.io.in_public == s1.io.in_public && s0.io.output == s1.io.output
  ensures r0.io.output == r1.io.output
  decreases d, c, t, s0, s1, r0, r1
{
}

lemma /*{:_induction d, s, e, t}*/ WellTypedExprSuccess(d: Declarations, s: Store, e: Expr, t: Type)
  requires StoreWellTyped(d, s)
  requires ExprHasType(d, e, t)
  ensures EvalExpr(e, s).ESuccess?
  decreases d, s, e, t
{
}

lemma /*{:_induction d, s, c}*/ WellTypedCommandSuccess(d: Declarations, s: State, c: Command)
  requires StoreWellTyped(d, s.store)
  requires CommandWellTyped(d, c)
  ensures EvalCommand(s, c).Timeout? || (EvalCommand(s, c).Success? && StoreWellTyped(d, EvalCommand(s, c).s))
  decreases s.fuel, c
{
}

lemma /*{:_induction d, s, c}*/ TypeSafety(d: Declarations, s: State, io: IO, c: Command)
  requires StoreWellTyped(d, s.store)
  requires CommandWellTyped(d, c)
  requires !EvalCommand(s, c).Timeout?
  ensures EvalCommand(s, c).Success? && StoreWellTyped(d, EvalCommand(s, c).s)
  decreases d, s, io, c
{
}

function method EvalExpr(e: Expr, store: Store): EResult
  decreases e, store
{
  match e
  case Bool(b) =>
    ESuccess(B(b))
  case Int(i) =>
    ESuccess(I(i))
  case Var(v) =>
    if v in store then
      ESuccess(store[v])
    else
      EFail
  case BinaryOp(op, left, right) =>
    var left := EvalExpr(left, store);
    var right := EvalExpr(right, store);
    if left.EFail? || right.EFail? then
      EFail
    else if left.v.I? && right.v.I? then
      match op
      case Plus =>
        ESuccess(I(left.v.i + right.v.i))
      case Sub =>
        ESuccess(I(left.v.i - right.v.i))
      case Times =>
        ESuccess(I(left.v.i * right.v.i))
      case Leq =>
        ESuccess(B(left.v.i <= right.v.i))
      case Eq =>
        ESuccess(B(left.v.i == right.v.i))
    else
      EFail
}

lemma ExprExamples()
{
}

function method {:extern} PrintString(s: string, ghost io: IO): (io': IO)
  ensures io' == io.(output := io.output + [s])
  decreases s, io

function method {:extern} ReadInt(ghost io: IO): (int, IO)
  ensures var (i: int, io': IO) := ReadInt(io); io' == io.(in_public := io.in_public + [i])
  decreases io

function method {:extern} ReadSecretInt(ghost io: IO): (int, IO)
  ensures var (i: int, io': IO) := ReadSecretInt(io); io' == io.(in_secret := io.in_secret + [i])
  decreases io

function method Bool2String(b: bool): string
  decreases b
{
  if b then
    ""true""
  else
    ""false""
}

function method {:extern} Int2String(i: int): string
  decreases i

function method EvalCommand(s: State, c: Command): CResult
  decreases s.fuel, c
{
  if s.fuel == 0 then
    Timeout
  else
    match c { case Noop => Success(s.store, s.io) case Assign(_mcc#0: Variable, _mcc#1: Expr) => (var e := _mcc#1; var variable := _mcc#0; var value := EvalExpr(e, s.store); match value case EFail => Fail case ESuccess(v) => Success(s.store[variable := v], s.io)) case Concat(_mcc#2: Command, _mcc#3: Command) => (var c1 := _mcc#3; var c0 := _mcc#2; var result0 := EvalCommand(s, c0); match result0 case Timeout => Timeout case Fail => Fail case Success(store', io') => EvalCommand(State(s.fuel, store', io'), c1)) case IfThenElse(_mcc#4: Expr, _mcc#5: Command, _mcc#6: Command) => (var ifFalse := _mcc#6; var ifTrue := _mcc#5; var cond := _mcc#4; var value := EvalExpr(cond, s.store); match value case EFail => Fail case ESuccess(I(_v0)) => Fail case ESuccess(B(b)) => if b then EvalCommand(s, ifTrue) else EvalCommand(s, ifFalse)) case While(_mcc#7: Expr, _mcc#8: Command) => (var body := _mcc#8; var cond := _mcc#7; var value := EvalExpr(cond, s.store); match value case EFail => Fail case ESuccess(I(_v1)) => Fail case ESuccess(B(b)) => if !b then Success(s.store, s.io) else EvalCommand(State(s.fuel - 1, s.store, s.io), Concat(body, c))) case PrintS(_mcc#9: string) => (var str := _mcc#9; var io' := PrintString(str, s.io); Success(s.store, io')) case PrintE(_mcc#10: Expr) => (var e := _mcc#10; var value := EvalExpr(e, s.store); match value case EFail => Fail case ESuccess(I(i)) => (var str := Int2String(i); var io' := PrintString(str, s.io); Success(s.store, io')) case ESuccess(B(b)) => var str := Bool2String(b); var io' := PrintString(str, s.io); Success(s.store, io')) case GetInt(_mcc#11: Variable) => (var variable := _mcc#11; var (i, io') := ReadInt(s.io.(in_secret := [])); Success(s.store[variable := I(i)], io'.(in_secret := s.io.in_secret))) case GetSecretInt(_mcc#12: Variable) => var variable := _mcc#12; var (i, io') := ReadSecretInt(s.io); Success(s.store[variable := I(i)], io') }
}

lemma CommandExamples(io: IO)
  decreases io
{
}

predicate method ExprHasType(d: Declarations, e: Expr, t: Type)
  decreases d, e, t
{
  match e
  case Bool(_) =>
    t.TBool?
  case Int(_) =>
    t.TInt?
  case Var(v) =>
    if v in d then
      d[v] == t
    else
      false
  case BinaryOp(op, lhs, rhs) =>
    var lhss := ExprHasType(d, lhs, TInt);
    var rhss := ExprHasType(d, rhs, TInt);
    match op
    case Plus =>
      lhss &&
      rhss &&
      t.TInt?
    case Sub =>
      lhss &&
      rhss &&
      t.TInt?
    case Times =>
      lhss &&
      rhss &&
      t.TInt?
    case Leq =>
      lhss &&
      rhss &&
      t.TBool?
    case Eq =>
      lhss &&
      rhss &&
      t.TBool?
}

predicate method CommandWellTyped(d: Declarations, c: Command)
  decreases d, c
{
  match c
  case Noop() =>
    true
  case Assign(variable, e) =>
    if variable in d then
      ExprHasType(d, e, d[variable])
    else
      false
  case Concat(c0, c1) =>
    CommandWellTyped(d, c0) &&
    CommandWellTyped(d, c1)
  case IfThenElse(cond, ifTrue, ifFalse) =>
    ExprHasType(d, cond, TBool) &&
    CommandWellTyped(d, ifTrue) &&
    CommandWellTyped(d, ifFalse)
  case While(cond, body) =>
    ExprHasType(d, cond, TBool) &&
    CommandWellTyped(d, body)
  case PrintS(str) =>
    true
  case PrintE(e) =>
    ExprHasType(d, e, TBool) || ExprHasType(d, e, TInt)
  case GetInt(variable) =>
    ExprHasType(d, Var(variable), TInt)
  case GetSecretInt(variable) =>
    ExprHasType(d, Var(variable), TInt)
}

lemma TypeExamples(io: IO)
  decreases io
{
}

predicate StoreWellTyped(d: Declarations, s: Store)
  decreases d, s
{
  forall variable: Variable :: 
    variable in d ==>
      variable in s &&
      (d[variable].TBool? ==>
        s[variable].B?) &&
      (d[variable].TInt? ==>
        s[variable].I?)
}

type VarTaintMap = map<Variable, bool>

datatype TaintState = TaintState(fuel: nat, store: Store, ghost io: IO, pc_tainted: bool, var_map: VarTaintMap)

datatype TaintValue = TV(tainted: bool, v: Value)

datatype TResult = TTimeout | TLeak | TSuccess(s: TaintState)

datatype SecType = Low | High

type SecDeclarations = map<Variable, SecType>

datatype Op = Plus | Sub | Times | Leq | Eq

datatype Variable = Variable(name: string)

datatype Expr = Bool(b: bool) | Int(i: int) | Var(v: Variable) | BinaryOp(op: Op, left: Expr, right: Expr)

datatype Command = Noop | Assign(v: Variable, e: Expr) | Concat(c0: Command, c1: Command) | IfThenElse(cond: Expr, ifTrue: Command, ifFalse: Command) | While(cond: Expr, body: Command) | PrintS(s: string) | PrintE(e: Expr) | GetInt(v: Variable) | GetSecretInt(v: Variable)

datatype Value = B(b: bool) | I(i: int)

datatype EResult = EFail | ESuccess(v: Value)

type Store = map<Variable, Value>

datatype IO = IO(ghost in_public: seq<int>, ghost in_secret: seq<int>, ghost output: seq<string>)

datatype CResult = Timeout | Fail | Success(s: Store, ghost io: IO)

datatype State = State(fuel: nat, store: Store, ghost io: IO)

datatype Type = TInt | TBool

type Declarations = map<Variable, Type>
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (other == null || Count != other.Count) {
        return false;
      } else if (this == other) {
        return true;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> {
    long LongCount { get; }
    int Count { get; }
    T[] Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var values = new T[len];
      for (int i = 0; i < len; i++) {
        values[i] = init(new BigInteger(i));
      }
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = (T[])sequence.Elements.Clone();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      T[] leftElmts = left.Elements, rightElmts = right.Elements;
      for (int i = 0; i < n; i++) {
        if (!object.Equals(leftElmts[i], rightElmts[i])) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n <= right.Elements.Length && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n < right.Elements.Length && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    protected abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements {
      get { return ImmutableElements.ToArray(); }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromCollection(ImmutableElements);
        return st.Elements;
      }
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      int n = ImmutableElements.Length;
      return n == other.Elements.Length && EqualUntil(this, other, n);
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      // This is required because (ImmutableElements is ImmutableArray<char>) is not a valid type check
      var typeCheckTmp = new T[0];
      ImmutableArray<T> elmts = ImmutableElements;
      if (typeCheckTmp is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      if (ImmutableElements.Length == m) {
        return this;
      }

      int length = checked((int)m);
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(0, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      int startingElement = checked((int)m);
      if (startingElement == 0) {
        return this;
      }

      int length = ImmutableElements.Length - startingElement;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingElement, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      if (n.IsZero) {
        return this;
      }

      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == ImmutableElements.Length) {
        return this;
      }
      int startingIndex = checked((int)lo);
      int endingIndex = checked((int)hi);
      var length = endingIndex - startingIndex;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingIndex, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }
    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private volatile ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>();
      var toVisit = new Stack<ISequence<T>>();
      var (leftBuffer, rightBuffer) = (left, right);
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          (leftBuffer, rightBuffer) = (cs.left, cs.right);
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          var array = seq.Elements;
          ansBuilder.AddRange(array);
        }
      }
      return ansBuilder.ToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
      }
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}

namespace @_System {
  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
  }

  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static _ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
public static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }
} // end of namespace _System
namespace _module {

  public partial class __default {
    public static void RunCommandTaintAnalysis(Dafny.ISequence<char> filename)
    {
      Dafny.IMap<_IVariable,_IType> _1014_decls;
      _ICommand _1015_cmd;
      Dafny.IMap<_IVariable,_IType> _out0;
      _ICommand _out1;
      __default.ParseFileNormal(filename, out _out0, out _out1);
      _1014_decls = _out0;
      _1015_cmd = _out1;
      if (!(__default.CommandWellTyped(_1014_decls, _1015_cmd))) {
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Sorry, the command is not well typed.\n"));
      } else {
        Dafny.IMap<_IVariable,_IValue> _1016_store;
        _1016_store = Dafny.Helpers.Id<Func<Dafny.IMap<_IVariable,_IType>, Dafny.IMap<_IVariable,_IValue>>>((_1017_decls) => ((System.Func<Dafny.IMap<_IVariable,_IValue>>)(() => {
          var _coll0 = new System.Collections.Generic.List<Dafny.Pair<_IVariable,_IValue>>();
          foreach (_IVariable _compr_0 in (_1017_decls).Keys.Elements) {
            _IVariable _1018_v = (_IVariable)_compr_0;
            if ((_1017_decls).Contains((_1018_v))) {
              _coll0.Add(new Dafny.Pair<_IVariable,_IValue>(_1018_v, (((Dafny.Map<_IVariable, _IType>.Select(_1017_decls,_1018_v)).is_TBool) ? (Value.create_B(false)) : (Value.create_I(BigInteger.Zero)))));
            }
          }
          return Dafny.Map<_IVariable,_IValue>.FromCollection(_coll0);
        }))())(_1014_decls);
        Dafny.IMap<_IVariable,bool> _1019_vars__map;
        _1019_vars__map = Dafny.Helpers.Id<Func<Dafny.IMap<_IVariable,_IType>, Dafny.IMap<_IVariable,bool>>>((_1020_decls) => ((System.Func<Dafny.IMap<_IVariable,bool>>)(() => {
          var _coll1 = new System.Collections.Generic.List<Dafny.Pair<_IVariable,bool>>();
          foreach (_IVariable _compr_1 in (_1020_decls).Keys.Elements) {
            _IVariable _1021_v = (_IVariable)_compr_1;
            if ((_1020_decls).Contains((_1021_v))) {
              _coll1.Add(new Dafny.Pair<_IVariable,bool>(_1021_v, false));
            }
          }
          return Dafny.Map<_IVariable,bool>.FromCollection(_coll1);
        }))())(_1014_decls);
        _ITaintState _1022_taint__state;
        _1022_taint__state = TaintState.create(new BigInteger(4294967295L), _1016_store, false, _1019_vars__map);
        _ITResult _1023_result;
        _1023_result = __default.EvalCommandTaint(_1014_decls, _1022_taint__state, _1015_cmd);
        _ITResult _source0 = _1023_result;
        if (_source0.is_TTimeout) {
          Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\nExecution timed out.  You probably have an infinite loop in your code.\n"));
        } else if (_source0.is_TLeak) {
          Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\nYour program tried to leak a secret, but we caught you!\n"));
        } else {
          _ITaintState _1024___mcc_h0 = _source0.dtor_s;
          Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\nCongratulations, your program ran to completion.\n"));
        }
      }
    }
    public static void RunCommandSecTypes(Dafny.ISequence<char> filename)
    {
      Dafny.IMap<_IVariable,_ISecType> _1025_decls;
      _ICommand _1026_cmd;
      Dafny.IMap<_IVariable,_ISecType> _out2;
      _ICommand _out3;
      __default.ParseFileSecTypes(filename, out _out2, out _out3);
      _1025_decls = _out2;
      _1026_cmd = _out3;
      if (__default.CommandHasSecType(_1025_decls, _1026_cmd, SecType.create_Low())) {
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Command is well typed at Low\n"));
      } else if (__default.CommandHasSecType(_1025_decls, _1026_cmd, SecType.create_High())) {
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Command is well typed at High\n"));
      } else {
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Sorry, the command is not well typed.\n"));
        return ;
      }
      Dafny.IMap<_IVariable,_IValue> _1027_store;
      _1027_store = Dafny.Helpers.Id<Func<Dafny.IMap<_IVariable,_ISecType>, Dafny.IMap<_IVariable,_IValue>>>((_1028_decls) => ((System.Func<Dafny.IMap<_IVariable,_IValue>>)(() => {
        var _coll2 = new System.Collections.Generic.List<Dafny.Pair<_IVariable,_IValue>>();
        foreach (_IVariable _compr_2 in (_1028_decls).Keys.Elements) {
          _IVariable _1029_v = (_IVariable)_compr_2;
          if ((_1028_decls).Contains((_1029_v))) {
            _coll2.Add(new Dafny.Pair<_IVariable,_IValue>(_1029_v, Value.create_B(false)));
          }
        }
        return Dafny.Map<_IVariable,_IValue>.FromCollection(_coll2);
      }))())(_1025_decls);
      _IState _1030_state;
      _1030_state = State.create(new BigInteger(4294967295L), _1027_store);
      _ICResult _1031_result;
      _1031_result = __default.EvalCommand(_1030_state, _1026_cmd);
      _ICResult _source1 = _1031_result;
      if (_source1.is_Timeout) {
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\nExecution timed out.  You probably have an infinite loop in your code.\n"));
      } else if (_source1.is_Fail) {
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\nSorry, your program failed during execution.\n"));
      } else {
        Dafny.IMap<_IVariable,_IValue> _1032___mcc_h0 = _source1.dtor_s;
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\nCongratulations, your program ran to completion.\n"));
      }
    }
    public static _ITaintValue EvalExprTaint(Dafny.IMap<_IVariable,_IType> d, _ITaintState s, _IExpr e, _IType t)
    {
      _IExpr _source2 = e;
      if (_source2.is_Bool) {
        bool _1033___mcc_h0 = _source2.dtor_b;
        bool _1034_b = _1033___mcc_h0;
        return TaintValue.create(false, Value.create_B(_1034_b));
      } else if (_source2.is_Int) {
        BigInteger _1035___mcc_h1 = _source2.dtor_i;
        BigInteger _1036_i = _1035___mcc_h1;
        return TaintValue.create(false, Value.create_I(_1036_i));
      } else if (_source2.is_Var) {
        _IVariable _1037___mcc_h2 = _source2.dtor_v;
        _IVariable _1038_v = _1037___mcc_h2;
        return TaintValue.create(Dafny.Map<_IVariable, bool>.Select((s).dtor_var__map,_1038_v), Dafny.Map<_IVariable, _IValue>.Select((s).dtor_store,_1038_v));
      } else {
        _IOp _1039___mcc_h3 = _source2.dtor_op;
        _IExpr _1040___mcc_h4 = _source2.dtor_left;
        _IExpr _1041___mcc_h5 = _source2.dtor_right;
        _IExpr _1042_rhs = _1041___mcc_h5;
        _IExpr _1043_lhs = _1040___mcc_h4;
        _IOp _1044_op = _1039___mcc_h3;
        _ITaintValue _1045_lhs = __default.EvalExprTaint(d, s, _1043_lhs, Type.create_TInt());
        _ITaintValue _1046_rhs = __default.EvalExprTaint(d, s, _1042_rhs, Type.create_TInt());
        if ((((_1045_lhs).dtor_tainted) == (true)) || (((_1046_rhs).dtor_tainted) == (true))) {
          _IOp _source3 = _1044_op;
          if (_source3.is_Plus) {
            return TaintValue.create(true, Value.create_I((((_1045_lhs).dtor_v).dtor_i) + (((_1046_rhs).dtor_v).dtor_i)));
          } else if (_source3.is_Sub) {
            return TaintValue.create(true, Value.create_I((((_1045_lhs).dtor_v).dtor_i) - (((_1046_rhs).dtor_v).dtor_i)));
          } else if (_source3.is_Times) {
            if (((((_1045_lhs).dtor_tainted) == (false)) && (object.Equals((_1045_lhs).dtor_v, Value.create_I(BigInteger.Zero)))) || ((((_1046_rhs).dtor_tainted) == (false)) && (object.Equals((_1046_rhs).dtor_v, Value.create_I(BigInteger.Zero))))) {
              return TaintValue.create(false, Value.create_I(BigInteger.Zero));
            } else {
              return TaintValue.create(true, Value.create_I((((_1045_lhs).dtor_v).dtor_i) * (((_1046_rhs).dtor_v).dtor_i)));
            }
          } else if (_source3.is_Leq) {
            return TaintValue.create(true, Value.create_B((((_1045_lhs).dtor_v).dtor_i) <= (((_1046_rhs).dtor_v).dtor_i)));
          } else {
            return TaintValue.create(true, Value.create_B((((_1045_lhs).dtor_v).dtor_i) == (((_1046_rhs).dtor_v).dtor_i)));
          }
        } else {
          _IOp _source4 = _1044_op;
          if (_source4.is_Plus) {
            return TaintValue.create(false, Value.create_I((((_1045_lhs).dtor_v).dtor_i) + (((_1046_rhs).dtor_v).dtor_i)));
          } else if (_source4.is_Sub) {
            return TaintValue.create(false, Value.create_I((((_1045_lhs).dtor_v).dtor_i) - (((_1046_rhs).dtor_v).dtor_i)));
          } else if (_source4.is_Times) {
            return TaintValue.create(false, Value.create_I((((_1045_lhs).dtor_v).dtor_i) * (((_1046_rhs).dtor_v).dtor_i)));
          } else if (_source4.is_Leq) {
            return TaintValue.create(false, Value.create_B((((_1045_lhs).dtor_v).dtor_i) <= (((_1046_rhs).dtor_v).dtor_i)));
          } else {
            return TaintValue.create(false, Value.create_B((((_1045_lhs).dtor_v).dtor_i) == (((_1046_rhs).dtor_v).dtor_i)));
          }
        }
      }
    }
    public static _ITaintState UpdateVarTaint(_ITaintState s, _IVariable v, bool taint)
    {
      _ITaintState _1047_dt__update__tmp_h0 = s;
      Dafny.IMap<_IVariable,bool> _1048_dt__update_hvar__map_h0 = Dafny.Map<_IVariable, bool>.Update((s).dtor_var__map, v, taint);
      return TaintState.create((_1047_dt__update__tmp_h0).dtor_fuel, (_1047_dt__update__tmp_h0).dtor_store, (_1047_dt__update__tmp_h0).dtor_pc__tainted, _1048_dt__update_hvar__map_h0);
    }
    public static _ITaintState UpdateVarVal(_ITaintState s, _IVariable v, _IValue val)
    {
      _ITaintState _1049_dt__update__tmp_h0 = s;
      Dafny.IMap<_IVariable,_IValue> _1050_dt__update_hstore_h0 = Dafny.Map<_IVariable, _IValue>.Update((s).dtor_store, v, val);
      return TaintState.create((_1049_dt__update__tmp_h0).dtor_fuel, _1050_dt__update_hstore_h0, (_1049_dt__update__tmp_h0).dtor_pc__tainted, (_1049_dt__update__tmp_h0).dtor_var__map);
    }
    public static _ITaintState UpdatePCTaint(_ITaintState s, bool taint)
    {
      _ITaintState _1051_dt__update__tmp_h0 = s;
      bool _1052_dt__update_hpc__tainted_h0 = taint;
      return TaintState.create((_1051_dt__update__tmp_h0).dtor_fuel, (_1051_dt__update__tmp_h0).dtor_store, _1052_dt__update_hpc__tainted_h0, (_1051_dt__update__tmp_h0).dtor_var__map);
    }
    public static _ITResult EvalCommandTaint(Dafny.IMap<_IVariable,_IType> d, _ITaintState s, _ICommand c)
    {
      if (((s).dtor_fuel).Sign == 0) {
        return TResult.create_TTimeout();
      } else {
        _ICommand _source5 = c;
        if (_source5.is_Noop) {
          return TResult.create_TSuccess(s);
        } else if (_source5.is_Assign) {
          _IVariable _1053___mcc_h0 = _source5.dtor_v;
          _IExpr _1054___mcc_h1 = _source5.dtor_e;
          _IExpr _1055_e = _1054___mcc_h1;
          _IVariable _1056_variable = _1053___mcc_h0;
          if ((!(Dafny.Map<_IVariable, bool>.Select((s).dtor_var__map,_1056_variable))) && ((s).dtor_pc__tainted)) {
            return TResult.create_TLeak();
          } else {
            _ITaintValue _let_tmp_rhs0 = __default.EvalExprTaint(d, s, _1055_e, Dafny.Map<_IVariable, _IType>.Select(d,_1056_variable));
            bool _1057_taint = _let_tmp_rhs0.dtor_tainted;
            _IValue _1058_value = _let_tmp_rhs0.dtor_v;
            bool _1059_new__taint = (_1057_taint) || ((s).dtor_pc__tainted);
            _ITaintState _1060_new__s = __default.UpdateVarTaint(s, _1056_variable, _1059_new__taint);
            _ITaintState _1061_s_k = __default.UpdateVarVal(_1060_new__s, _1056_variable, _1058_value);
            return TResult.create_TSuccess(_1061_s_k);
          }
        } else if (_source5.is_Concat) {
          _ICommand _1062___mcc_h2 = _source5.dtor_c0;
          _ICommand _1063___mcc_h3 = _source5.dtor_c1;
          _ICommand _1064_c1 = _1063___mcc_h3;
          _ICommand _1065_c0 = _1062___mcc_h2;
          _ITResult _1066_result0 = __default.EvalCommandTaint(d, s, _1065_c0);
          _ITResult _source6 = _1066_result0;
          if (_source6.is_TTimeout) {
            return TResult.create_TTimeout();
          } else if (_source6.is_TLeak) {
            return TResult.create_TLeak();
          } else {
            _ITaintState _1067___mcc_h13 = _source6.dtor_s;
            _ITaintState _1068_s_k = _1067___mcc_h13;
            return __default.EvalCommandTaint(d, Dafny.Helpers.Let<_ITaintState, _ITaintState>(_1068_s_k, _pat_let0_0 => Dafny.Helpers.Let<_ITaintState, _ITaintState>(_pat_let0_0, _1069_dt__update__tmp_h0 => Dafny.Helpers.Let<BigInteger, _ITaintState>((s).dtor_fuel, _pat_let1_0 => Dafny.Helpers.Let<BigInteger, _ITaintState>(_pat_let1_0, _1070_dt__update_hfuel_h0 => TaintState.create(_1070_dt__update_hfuel_h0, (_1069_dt__update__tmp_h0).dtor_store, (_1069_dt__update__tmp_h0).dtor_pc__tainted, (_1069_dt__update__tmp_h0).dtor_var__map))))), _1064_c1);
          }
        } else if (_source5.is_IfThenElse) {
          _IExpr _1071___mcc_h4 = _source5.dtor_cond;
          _ICommand _1072___mcc_h5 = _source5.dtor_ifTrue;
          _ICommand _1073___mcc_h6 = _source5.dtor_ifFalse;
          _ICommand _1074_ifFalse = _1073___mcc_h6;
          _ICommand _1075_ifTrue = _1072___mcc_h5;
          _IExpr _1076_cond = _1071___mcc_h4;
          _ITaintValue _let_tmp_rhs1 = __default.EvalExprTaint(d, s, _1076_cond, Type.create_TBool());
          bool _1077_taint = _let_tmp_rhs1.dtor_tainted;
          _IValue _let_tmp_rhs2 = _let_tmp_rhs1.dtor_v;
          bool _1078_b = _let_tmp_rhs2.dtor_b;
          if (_1078_b) {
            _ITaintState _1079_new__s = ((_1077_taint) ? (__default.UpdatePCTaint(s, true)) : (s));
            _ITResult _1080_result = __default.EvalCommandTaint(d, _1079_new__s, _1075_ifTrue);
            _ITResult _source7 = _1080_result;
            if (_source7.is_TTimeout) {
              return TResult.create_TTimeout();
            } else if (_source7.is_TLeak) {
              return TResult.create_TLeak();
            } else {
              _ITaintState _1081___mcc_h14 = _source7.dtor_s;
              _ITaintState _1082_s_k = _1081___mcc_h14;
              return TResult.create_TSuccess(__default.UpdatePCTaint(_1082_s_k, (s).dtor_pc__tainted));
            }
          } else {
            _ITaintState _1083_new__s = ((_1077_taint) ? (__default.UpdatePCTaint(s, true)) : (s));
            _ITResult _1084_result = __default.EvalCommandTaint(d, _1083_new__s, _1074_ifFalse);
            _ITResult _source8 = _1084_result;
            if (_source8.is_TTimeout) {
              return TResult.create_TTimeout();
            } else if (_source8.is_TLeak) {
              return TResult.create_TLeak();
            } else {
              _ITaintState _1085___mcc_h15 = _source8.dtor_s;
              _ITaintState _1086_s_k = _1085___mcc_h15;
              return TResult.create_TSuccess(__default.UpdatePCTaint(_1086_s_k, (s).dtor_pc__tainted));
            }
          }
        } else if (_source5.is_While) {
          _IExpr _1087___mcc_h7 = _source5.dtor_cond;
          _ICommand _1088___mcc_h8 = _source5.dtor_body;
          _ICommand _1089_body = _1088___mcc_h8;
          _IExpr _1090_cond = _1087___mcc_h7;
          _ITaintValue _let_tmp_rhs3 = __default.EvalExprTaint(d, s, _1090_cond, Type.create_TBool());
          bool _1091_taint = _let_tmp_rhs3.dtor_tainted;
          _IValue _let_tmp_rhs4 = _let_tmp_rhs3.dtor_v;
          bool _1092_b = _let_tmp_rhs4.dtor_b;
          if (!(_1092_b)) {
            return TResult.create_TSuccess(s);
          } else {
            _ITaintState _1093_new__s = ((_1091_taint) ? (__default.UpdatePCTaint(s, true)) : (s));
            _ITResult _1094_result = __default.EvalCommandTaint(d, Dafny.Helpers.Let<_ITaintState, _ITaintState>(_1093_new__s, _pat_let2_0 => Dafny.Helpers.Let<_ITaintState, _ITaintState>(_pat_let2_0, _1095_dt__update__tmp_h1 => Dafny.Helpers.Let<BigInteger, _ITaintState>(((s).dtor_fuel) - (BigInteger.One), _pat_let3_0 => Dafny.Helpers.Let<BigInteger, _ITaintState>(_pat_let3_0, _1096_dt__update_hfuel_h1 => TaintState.create(_1096_dt__update_hfuel_h1, (_1095_dt__update__tmp_h1).dtor_store, (_1095_dt__update__tmp_h1).dtor_pc__tainted, (_1095_dt__update__tmp_h1).dtor_var__map))))), Command.create_Concat(_1089_body, c));
            _ITResult _source9 = _1094_result;
            if (_source9.is_TTimeout) {
              return TResult.create_TTimeout();
            } else if (_source9.is_TLeak) {
              return TResult.create_TLeak();
            } else {
              _ITaintState _1097___mcc_h16 = _source9.dtor_s;
              _ITaintState _1098_s_k = _1097___mcc_h16;
              return TResult.create_TSuccess(__default.UpdatePCTaint(_1098_s_k, (s).dtor_pc__tainted));
            }
          }
        } else if (_source5.is_PrintS) {
          Dafny.ISequence<char> _1099___mcc_h9 = _source5.dtor_s;
          Dafny.ISequence<char> _1100_str = _1099___mcc_h9;
          if ((s).dtor_pc__tainted) {
            return TResult.create_TLeak();
          } else {
            _IIO _1101_io_k = __default.PrintString(_1100_str);
            return TResult.create_TSuccess(Dafny.Helpers.Let<_ITaintState, _ITaintState>(s, _pat_let4_0 => Dafny.Helpers.Let<_ITaintState, _ITaintState>(_pat_let4_0, _1102_dt__update__tmp_h2 => TaintState.create((_1102_dt__update__tmp_h2).dtor_fuel, (_1102_dt__update__tmp_h2).dtor_store, (_1102_dt__update__tmp_h2).dtor_pc__tainted, (_1102_dt__update__tmp_h2).dtor_var__map))));
          }
        } else if (_source5.is_PrintE) {
          _IExpr _1103___mcc_h10 = _source5.dtor_e;
          _IExpr _1104_e = _1103___mcc_h10;
          if ((s).dtor_pc__tainted) {
            return TResult.create_TLeak();
          } else {
            _IEResult _1105_value = __default.EvalExpr(_1104_e, (s).dtor_store);
            _IEResult _source10 = _1105_value;
            if (_source10.is_EFail) {
              return TResult.create_TSuccess(s);
            } else {
              _IValue _1106___mcc_h17 = _source10.dtor_v;
              _IValue _source11 = _1106___mcc_h17;
              if (_source11.is_B) {
                bool _1107___mcc_h18 = _source11.dtor_b;
                bool _1108_b = _1107___mcc_h18;
                _ITaintValue _let_tmp_rhs5 = __default.EvalExprTaint(d, s, _1104_e, Type.create_TBool());
                bool _1109_taint = _let_tmp_rhs5.dtor_tainted;
                _IValue _let_tmp_rhs6 = _let_tmp_rhs5.dtor_v;
                bool _1110_b = _let_tmp_rhs6.dtor_b;
                Dafny.ISequence<char> _1111_str = __default.Bool2String(_1110_b);
                _IIO _1112_io_k = __default.PrintString(_1111_str);
                _ITaintState _1113_s_k = Dafny.Helpers.Let<_ITaintState, _ITaintState>(s, _pat_let5_0 => Dafny.Helpers.Let<_ITaintState, _ITaintState>(_pat_let5_0, _1114_dt__update__tmp_h3 => TaintState.create((_1114_dt__update__tmp_h3).dtor_fuel, (_1114_dt__update__tmp_h3).dtor_store, (_1114_dt__update__tmp_h3).dtor_pc__tainted, (_1114_dt__update__tmp_h3).dtor_var__map)));
                if (_1109_taint) {
                  return TResult.create_TLeak();
                } else {
                  return TResult.create_TSuccess(_1113_s_k);
                }
              } else {
                BigInteger _1115___mcc_h19 = _source11.dtor_i;
                BigInteger _1116_i = _1115___mcc_h19;
                _ITaintValue _let_tmp_rhs7 = __default.EvalExprTaint(d, s, _1104_e, Type.create_TInt());
                bool _1117_taint = _let_tmp_rhs7.dtor_tainted;
                _IValue _1118_value = _let_tmp_rhs7.dtor_v;
                Dafny.ISequence<char> _1119_str = __default.Int2String(_1116_i);
                _IIO _1120_io_k = __default.PrintString(_1119_str);
                _ITaintState _1121_s_k = Dafny.Helpers.Let<_ITaintState, _ITaintState>(s, _pat_let6_0 => Dafny.Helpers.Let<_ITaintState, _ITaintState>(_pat_let6_0, _1122_dt__update__tmp_h4 => TaintState.create((_1122_dt__update__tmp_h4).dtor_fuel, (_1122_dt__update__tmp_h4).dtor_store, (_1122_dt__update__tmp_h4).dtor_pc__tainted, (_1122_dt__update__tmp_h4).dtor_var__map)));
                if (_1117_taint) {
                  return TResult.create_TLeak();
                } else {
                  return TResult.create_TSuccess(_1121_s_k);
                }
              }
            }
          }
        } else if (_source5.is_GetInt) {
          _IVariable _1123___mcc_h11 = _source5.dtor_v;
          _IVariable _1124_variable = _1123___mcc_h11;
          if ((s).dtor_pc__tainted) {
            return TResult.create_TLeak();
          } else {
            _System._ITuple2<BigInteger, _IIO> _let_tmp_rhs8 = __default.ReadInt();
            BigInteger _1125_i = _let_tmp_rhs8.dtor__0;
            _IIO _1126_io_k = _let_tmp_rhs8.dtor__1;
            Dafny.IMap<_IVariable,_IValue> _1127_new__store = Dafny.Map<_IVariable, _IValue>.Update((s).dtor_store, _1124_variable, Value.create_I(_1125_i));
            _ITaintState _1128_new__s = __default.UpdateVarTaint(s, _1124_variable, false);
            return TResult.create_TSuccess(TaintState.create((s).dtor_fuel, _1127_new__store, (_1128_new__s).dtor_pc__tainted, (_1128_new__s).dtor_var__map));
          }
        } else {
          _IVariable _1129___mcc_h12 = _source5.dtor_v;
          _IVariable _1130_variable = _1129___mcc_h12;
          if ((!(Dafny.Map<_IVariable, bool>.Select((s).dtor_var__map,_1130_variable))) && ((s).dtor_pc__tainted)) {
            return TResult.create_TLeak();
          } else {
            _System._ITuple2<BigInteger, _IIO> _let_tmp_rhs9 = __default.ReadSecretInt();
            BigInteger _1131_i = _let_tmp_rhs9.dtor__0;
            _IIO _1132_io_k = _let_tmp_rhs9.dtor__1;
            Dafny.IMap<_IVariable,_IValue> _1133_new__store = Dafny.Map<_IVariable, _IValue>.Update((s).dtor_store, _1130_variable, Value.create_I(_1131_i));
            _ITaintState _1134_new__s = __default.UpdateVarTaint(s, _1130_variable, true);
            return TResult.create_TSuccess(TaintState.create((s).dtor_fuel, _1133_new__store, (_1134_new__s).dtor_pc__tainted, (_1134_new__s).dtor_var__map));
          }
        }
      }
    }
    public static bool ExprHasSecType(Dafny.IMap<_IVariable,_ISecType> d, _IExpr e, _ISecType t)
    {
      _IExpr _source12 = e;
      if (_source12.is_Bool) {
        bool _1135___mcc_h0 = _source12.dtor_b;
        return true;
      } else if (_source12.is_Int) {
        BigInteger _1136___mcc_h1 = _source12.dtor_i;
        return true;
      } else if (_source12.is_Var) {
        _IVariable _1137___mcc_h2 = _source12.dtor_v;
        _IVariable _1138_v = _1137___mcc_h2;
        if ((d).Contains((_1138_v))) {
          return object.Equals(Dafny.Map<_IVariable, _ISecType>.Select(d,_1138_v), t);
        } else {
          return false;
        }
      } else {
        _IOp _1139___mcc_h3 = _source12.dtor_op;
        _IExpr _1140___mcc_h4 = _source12.dtor_left;
        _IExpr _1141___mcc_h5 = _source12.dtor_right;
        _IExpr _1142_right = _1141___mcc_h5;
        _IExpr _1143_left = _1140___mcc_h4;
        _IOp _1144_op = _1139___mcc_h3;
        return (__default.ExprHasSecType(d, _1143_left, t)) && (__default.ExprHasSecType(d, _1142_right, t));
      }
    }
    public static bool CommandHasSecTypeBasic(Dafny.IMap<_IVariable,_ISecType> d, _ICommand c, _ISecType t)
    {
      _ICommand _source13 = c;
      if (_source13.is_Noop) {
        return true;
      } else if (_source13.is_Assign) {
        _IVariable _1145___mcc_h0 = _source13.dtor_v;
        _IExpr _1146___mcc_h1 = _source13.dtor_e;
        _IExpr _1147_e = _1146___mcc_h1;
        _IVariable _1148_variable = _1145___mcc_h0;
        if ((d).Contains((_1148_variable))) {
          return (object.Equals(Dafny.Map<_IVariable, _ISecType>.Select(d,_1148_variable), t)) && (__default.ExprHasSecType(d, _1147_e, t));
        } else {
          return false;
        }
      } else if (_source13.is_Concat) {
        _ICommand _1149___mcc_h2 = _source13.dtor_c0;
        _ICommand _1150___mcc_h3 = _source13.dtor_c1;
        _ICommand _1151_c1 = _1150___mcc_h3;
        _ICommand _1152_c0 = _1149___mcc_h2;
        return (__default.CommandHasSecType(d, _1152_c0, t)) && (__default.CommandHasSecType(d, _1151_c1, t));
      } else if (_source13.is_IfThenElse) {
        _IExpr _1153___mcc_h4 = _source13.dtor_cond;
        _ICommand _1154___mcc_h5 = _source13.dtor_ifTrue;
        _ICommand _1155___mcc_h6 = _source13.dtor_ifFalse;
        _ICommand _1156_ifFalse = _1155___mcc_h6;
        _ICommand _1157_ifTrue = _1154___mcc_h5;
        _IExpr _1158_cond = _1153___mcc_h4;
        return ((__default.ExprHasSecType(d, _1158_cond, t)) && (__default.CommandHasSecType(d, _1157_ifTrue, t))) && (__default.CommandHasSecType(d, _1156_ifFalse, t));
      } else if (_source13.is_While) {
        _IExpr _1159___mcc_h7 = _source13.dtor_cond;
        _ICommand _1160___mcc_h8 = _source13.dtor_body;
        _ICommand _1161_body = _1160___mcc_h8;
        _IExpr _1162_cond = _1159___mcc_h7;
        return (__default.ExprHasSecType(d, _1162_cond, t)) && (__default.CommandHasSecType(d, _1161_body, t));
      } else if (_source13.is_PrintS) {
        Dafny.ISequence<char> _1163___mcc_h9 = _source13.dtor_s;
        Dafny.ISequence<char> _1164_str = _1163___mcc_h9;
        if (object.Equals(t, SecType.create_Low())) {
          return true;
        } else {
          return false;
        }
      } else if (_source13.is_PrintE) {
        _IExpr _1165___mcc_h10 = _source13.dtor_e;
        _IExpr _1166_e = _1165___mcc_h10;
        return (__default.ExprHasSecType(d, _1166_e, SecType.create_Low())) && (object.Equals(t, SecType.create_Low()));
      } else if (_source13.is_GetInt) {
        _IVariable _1167___mcc_h11 = _source13.dtor_v;
        _IVariable _1168_variable = _1167___mcc_h11;
        return (__default.ExprHasSecType(d, Expr.create_Var(_1168_variable), SecType.create_Low())) && (object.Equals(t, SecType.create_Low()));
      } else {
        _IVariable _1169___mcc_h12 = _source13.dtor_v;
        _IVariable _1170_variable = _1169___mcc_h12;
        return (__default.ExprHasSecType(d, Expr.create_Var(_1170_variable), SecType.create_High())) && (object.Equals(t, SecType.create_High()));
      }
    }
    public static bool CommandHasSecType(Dafny.IMap<_IVariable,_ISecType> d, _ICommand c, _ISecType t)
    {
      return (__default.CommandHasSecTypeBasic(d, c, t)) || (((t).is_Low) && (__default.CommandHasSecTypeBasic(d, c, SecType.create_High())));
    }
    public static _IEResult EvalExpr(_IExpr e, Dafny.IMap<_IVariable,_IValue> store)
    {
      _IExpr _source14 = e;
      if (_source14.is_Bool) {
        bool _1171___mcc_h0 = _source14.dtor_b;
        bool _1172_b = _1171___mcc_h0;
        return EResult.create_ESuccess(Value.create_B(_1172_b));
      } else if (_source14.is_Int) {
        BigInteger _1173___mcc_h1 = _source14.dtor_i;
        BigInteger _1174_i = _1173___mcc_h1;
        return EResult.create_ESuccess(Value.create_I(_1174_i));
      } else if (_source14.is_Var) {
        _IVariable _1175___mcc_h2 = _source14.dtor_v;
        _IVariable _1176_v = _1175___mcc_h2;
        if ((store).Contains((_1176_v))) {
          return EResult.create_ESuccess(Dafny.Map<_IVariable, _IValue>.Select(store,_1176_v));
        } else {
          return EResult.create_EFail();
        }
      } else {
        _IOp _1177___mcc_h3 = _source14.dtor_op;
        _IExpr _1178___mcc_h4 = _source14.dtor_left;
        _IExpr _1179___mcc_h5 = _source14.dtor_right;
        _IExpr _1180_right = _1179___mcc_h5;
        _IExpr _1181_left = _1178___mcc_h4;
        _IOp _1182_op = _1177___mcc_h3;
        _IEResult _1183_left = __default.EvalExpr(_1181_left, store);
        _IEResult _1184_right = __default.EvalExpr(_1180_right, store);
        if (((_1183_left).is_EFail) || ((_1184_right).is_EFail)) {
          return EResult.create_EFail();
        } else if ((((_1183_left).dtor_v).is_I) && (((_1184_right).dtor_v).is_I)) {
          _IOp _source15 = _1182_op;
          if (_source15.is_Plus) {
            return EResult.create_ESuccess(Value.create_I((((_1183_left).dtor_v).dtor_i) + (((_1184_right).dtor_v).dtor_i)));
          } else if (_source15.is_Sub) {
            return EResult.create_ESuccess(Value.create_I((((_1183_left).dtor_v).dtor_i) - (((_1184_right).dtor_v).dtor_i)));
          } else if (_source15.is_Times) {
            return EResult.create_ESuccess(Value.create_I((((_1183_left).dtor_v).dtor_i) * (((_1184_right).dtor_v).dtor_i)));
          } else if (_source15.is_Leq) {
            return EResult.create_ESuccess(Value.create_B((((_1183_left).dtor_v).dtor_i) <= (((_1184_right).dtor_v).dtor_i)));
          } else {
            return EResult.create_ESuccess(Value.create_B((((_1183_left).dtor_v).dtor_i) == (((_1184_right).dtor_v).dtor_i)));
          }
        } else {
          return EResult.create_EFail();
        }
      }
    }
    public static Dafny.ISequence<char> Bool2String(bool b) {
      if (b) {
        return Dafny.Sequence<char>.FromString("true");
      } else {
        return Dafny.Sequence<char>.FromString("false");
      }
    }
    public static _ICResult EvalCommand(_IState s, _ICommand c)
    {
      if (((s).dtor_fuel).Sign == 0) {
        return CResult.create_Timeout();
      } else {
        _ICommand _source16 = c;
        if (_source16.is_Noop) {
          return CResult.create_Success((s).dtor_store);
        } else if (_source16.is_Assign) {
          _IVariable _1185___mcc_h0 = _source16.dtor_v;
          _IExpr _1186___mcc_h1 = _source16.dtor_e;
          _IExpr _1187_e = _1186___mcc_h1;
          _IVariable _1188_variable = _1185___mcc_h0;
          _IEResult _1189_value = __default.EvalExpr(_1187_e, (s).dtor_store);
          _IEResult _source17 = _1189_value;
          if (_source17.is_EFail) {
            return CResult.create_Fail();
          } else {
            _IValue _1190___mcc_h13 = _source17.dtor_v;
            _IValue _1191_v = _1190___mcc_h13;
            return CResult.create_Success(Dafny.Map<_IVariable, _IValue>.Update((s).dtor_store, _1188_variable, _1191_v));
          }
        } else if (_source16.is_Concat) {
          _ICommand _1192___mcc_h2 = _source16.dtor_c0;
          _ICommand _1193___mcc_h3 = _source16.dtor_c1;
          _ICommand _1194_c1 = _1193___mcc_h3;
          _ICommand _1195_c0 = _1192___mcc_h2;
          _ICResult _1196_result0 = __default.EvalCommand(s, _1195_c0);
          _ICResult _source18 = _1196_result0;
          if (_source18.is_Timeout) {
            return CResult.create_Timeout();
          } else if (_source18.is_Fail) {
            return CResult.create_Fail();
          } else {
            Dafny.IMap<_IVariable,_IValue> _1197___mcc_h14 = _source18.dtor_s;
            Dafny.IMap<_IVariable,_IValue> _1198_store_k = _1197___mcc_h14;
            return __default.EvalCommand(State.create((s).dtor_fuel, _1198_store_k), _1194_c1);
          }
        } else if (_source16.is_IfThenElse) {
          _IExpr _1199___mcc_h4 = _source16.dtor_cond;
          _ICommand _1200___mcc_h5 = _source16.dtor_ifTrue;
          _ICommand _1201___mcc_h6 = _source16.dtor_ifFalse;
          _ICommand _1202_ifFalse = _1201___mcc_h6;
          _ICommand _1203_ifTrue = _1200___mcc_h5;
          _IExpr _1204_cond = _1199___mcc_h4;
          _IEResult _1205_value = __default.EvalExpr(_1204_cond, (s).dtor_store);
          _IEResult _source19 = _1205_value;
          if (_source19.is_EFail) {
            return CResult.create_Fail();
          } else {
            _IValue _1206___mcc_h16 = _source19.dtor_v;
            _IValue _source20 = _1206___mcc_h16;
            if (_source20.is_B) {
              bool _1207___mcc_h17 = _source20.dtor_b;
              bool _1208_b = _1207___mcc_h17;
              if (_1208_b) {
                return __default.EvalCommand(s, _1203_ifTrue);
              } else {
                return __default.EvalCommand(s, _1202_ifFalse);
              }
            } else {
              BigInteger _1209___mcc_h18 = _source20.dtor_i;
              return CResult.create_Fail();
            }
          }
        } else if (_source16.is_While) {
          _IExpr _1210___mcc_h7 = _source16.dtor_cond;
          _ICommand _1211___mcc_h8 = _source16.dtor_body;
          _ICommand _1212_body = _1211___mcc_h8;
          _IExpr _1213_cond = _1210___mcc_h7;
          _IEResult _1214_value = __default.EvalExpr(_1213_cond, (s).dtor_store);
          _IEResult _source21 = _1214_value;
          if (_source21.is_EFail) {
            return CResult.create_Fail();
          } else {
            _IValue _1215___mcc_h19 = _source21.dtor_v;
            _IValue _source22 = _1215___mcc_h19;
            if (_source22.is_B) {
              bool _1216___mcc_h20 = _source22.dtor_b;
              bool _1217_b = _1216___mcc_h20;
              if (!(_1217_b)) {
                return CResult.create_Success((s).dtor_store);
              } else {
                return __default.EvalCommand(State.create(((s).dtor_fuel) - (BigInteger.One), (s).dtor_store), Command.create_Concat(_1212_body, c));
              }
            } else {
              BigInteger _1218___mcc_h21 = _source22.dtor_i;
              return CResult.create_Fail();
            }
          }
        } else if (_source16.is_PrintS) {
          Dafny.ISequence<char> _1219___mcc_h9 = _source16.dtor_s;
          Dafny.ISequence<char> _1220_str = _1219___mcc_h9;
          _IIO _1221_io_k = __default.PrintString(_1220_str);
          return CResult.create_Success((s).dtor_store);
        } else if (_source16.is_PrintE) {
          _IExpr _1222___mcc_h10 = _source16.dtor_e;
          _IExpr _1223_e = _1222___mcc_h10;
          _IEResult _1224_value = __default.EvalExpr(_1223_e, (s).dtor_store);
          _IEResult _source23 = _1224_value;
          if (_source23.is_EFail) {
            return CResult.create_Fail();
          } else {
            _IValue _1225___mcc_h22 = _source23.dtor_v;
            _IValue _source24 = _1225___mcc_h22;
            if (_source24.is_B) {
              bool _1226___mcc_h23 = _source24.dtor_b;
              bool _1227_b = _1226___mcc_h23;
              Dafny.ISequence<char> _1228_str = __default.Bool2String(_1227_b);
              _IIO _1229_io_k = __default.PrintString(_1228_str);
              return CResult.create_Success((s).dtor_store);
            } else {
              BigInteger _1230___mcc_h24 = _source24.dtor_i;
              BigInteger _1231_i = _1230___mcc_h24;
              Dafny.ISequence<char> _1232_str = __default.Int2String(_1231_i);
              _IIO _1233_io_k = __default.PrintString(_1232_str);
              return CResult.create_Success((s).dtor_store);
            }
          }
        } else if (_source16.is_GetInt) {
          _IVariable _1234___mcc_h11 = _source16.dtor_v;
          _IVariable _1235_variable = _1234___mcc_h11;
          _System._ITuple2<BigInteger, _IIO> _let_tmp_rhs10 = __default.ReadInt();
          BigInteger _1236_i = _let_tmp_rhs10.dtor__0;
          _IIO _1237_io_k = _let_tmp_rhs10.dtor__1;
          return CResult.create_Success(Dafny.Map<_IVariable, _IValue>.Update((s).dtor_store, _1235_variable, Value.create_I(_1236_i)));
        } else {
          _IVariable _1238___mcc_h12 = _source16.dtor_v;
          _IVariable _1239_variable = _1238___mcc_h12;
          _System._ITuple2<BigInteger, _IIO> _let_tmp_rhs11 = __default.ReadSecretInt();
          BigInteger _1240_i = _let_tmp_rhs11.dtor__0;
          _IIO _1241_io_k = _let_tmp_rhs11.dtor__1;
          return CResult.create_Success(Dafny.Map<_IVariable, _IValue>.Update((s).dtor_store, _1239_variable, Value.create_I(_1240_i)));
        }
      }
    }
    public static bool ExprHasType(Dafny.IMap<_IVariable,_IType> d, _IExpr e, _IType t)
    {
      _IExpr _source25 = e;
      if (_source25.is_Bool) {
        bool _1242___mcc_h0 = _source25.dtor_b;
        return (t).is_TBool;
      } else if (_source25.is_Int) {
        BigInteger _1243___mcc_h1 = _source25.dtor_i;
        return (t).is_TInt;
      } else if (_source25.is_Var) {
        _IVariable _1244___mcc_h2 = _source25.dtor_v;
        _IVariable _1245_v = _1244___mcc_h2;
        if ((d).Contains((_1245_v))) {
          return object.Equals(Dafny.Map<_IVariable, _IType>.Select(d,_1245_v), t);
        } else {
          return false;
        }
      } else {
        _IOp _1246___mcc_h3 = _source25.dtor_op;
        _IExpr _1247___mcc_h4 = _source25.dtor_left;
        _IExpr _1248___mcc_h5 = _source25.dtor_right;
        _IExpr _1249_rhs = _1248___mcc_h5;
        _IExpr _1250_lhs = _1247___mcc_h4;
        _IOp _1251_op = _1246___mcc_h3;
        bool _1252_lhss = __default.ExprHasType(d, _1250_lhs, Type.create_TInt());
        bool _1253_rhss = __default.ExprHasType(d, _1249_rhs, Type.create_TInt());
        _IOp _source26 = _1251_op;
        if (_source26.is_Plus) {
          return ((_1252_lhss) && (_1253_rhss)) && ((t).is_TInt);
        } else if (_source26.is_Sub) {
          return ((_1252_lhss) && (_1253_rhss)) && ((t).is_TInt);
        } else if (_source26.is_Times) {
          return ((_1252_lhss) && (_1253_rhss)) && ((t).is_TInt);
        } else if (_source26.is_Leq) {
          return ((_1252_lhss) && (_1253_rhss)) && ((t).is_TBool);
        } else {
          return ((_1252_lhss) && (_1253_rhss)) && ((t).is_TBool);
        }
      }
    }
    public static bool CommandWellTyped(Dafny.IMap<_IVariable,_IType> d, _ICommand c)
    {
      _ICommand _source27 = c;
      if (_source27.is_Noop) {
        return true;
      } else if (_source27.is_Assign) {
        _IVariable _1254___mcc_h0 = _source27.dtor_v;
        _IExpr _1255___mcc_h1 = _source27.dtor_e;
        _IExpr _1256_e = _1255___mcc_h1;
        _IVariable _1257_variable = _1254___mcc_h0;
        if ((d).Contains((_1257_variable))) {
          return __default.ExprHasType(d, _1256_e, Dafny.Map<_IVariable, _IType>.Select(d,_1257_variable));
        } else {
          return false;
        }
      } else if (_source27.is_Concat) {
        _ICommand _1258___mcc_h2 = _source27.dtor_c0;
        _ICommand _1259___mcc_h3 = _source27.dtor_c1;
        _ICommand _1260_c1 = _1259___mcc_h3;
        _ICommand _1261_c0 = _1258___mcc_h2;
        return (__default.CommandWellTyped(d, _1261_c0)) && (__default.CommandWellTyped(d, _1260_c1));
      } else if (_source27.is_IfThenElse) {
        _IExpr _1262___mcc_h4 = _source27.dtor_cond;
        _ICommand _1263___mcc_h5 = _source27.dtor_ifTrue;
        _ICommand _1264___mcc_h6 = _source27.dtor_ifFalse;
        _ICommand _1265_ifFalse = _1264___mcc_h6;
        _ICommand _1266_ifTrue = _1263___mcc_h5;
        _IExpr _1267_cond = _1262___mcc_h4;
        return ((__default.ExprHasType(d, _1267_cond, Type.create_TBool())) && (__default.CommandWellTyped(d, _1266_ifTrue))) && (__default.CommandWellTyped(d, _1265_ifFalse));
      } else if (_source27.is_While) {
        _IExpr _1268___mcc_h7 = _source27.dtor_cond;
        _ICommand _1269___mcc_h8 = _source27.dtor_body;
        _ICommand _1270_body = _1269___mcc_h8;
        _IExpr _1271_cond = _1268___mcc_h7;
        return (__default.ExprHasType(d, _1271_cond, Type.create_TBool())) && (__default.CommandWellTyped(d, _1270_body));
      } else if (_source27.is_PrintS) {
        Dafny.ISequence<char> _1272___mcc_h9 = _source27.dtor_s;
        Dafny.ISequence<char> _1273_str = _1272___mcc_h9;
        return true;
      } else if (_source27.is_PrintE) {
        _IExpr _1274___mcc_h10 = _source27.dtor_e;
        _IExpr _1275_e = _1274___mcc_h10;
        return (__default.ExprHasType(d, _1275_e, Type.create_TBool())) || (__default.ExprHasType(d, _1275_e, Type.create_TInt()));
      } else if (_source27.is_GetInt) {
        _IVariable _1276___mcc_h11 = _source27.dtor_v;
        _IVariable _1277_variable = _1276___mcc_h11;
        return __default.ExprHasType(d, Expr.create_Var(_1277_variable), Type.create_TInt());
      } else {
        _IVariable _1278___mcc_h12 = _source27.dtor_v;
        _IVariable _1279_variable = _1278___mcc_h12;
        return __default.ExprHasType(d, Expr.create_Var(_1279_variable), Type.create_TInt());
      }
    }
  }

  public interface _ITaintState {
    bool is_TaintState { get; }
    BigInteger dtor_fuel { get; }
    Dafny.IMap<_IVariable,_IValue> dtor_store { get; }
    bool dtor_pc__tainted { get; }
    Dafny.IMap<_IVariable,bool> dtor_var__map { get; }
    _ITaintState DowncastClone();
  }
  public class TaintState : _ITaintState {
    public readonly BigInteger fuel;
    public readonly Dafny.IMap<_IVariable,_IValue> store;
    public readonly bool pc__tainted;
    public readonly Dafny.IMap<_IVariable,bool> var__map;
    public TaintState(BigInteger fuel, Dafny.IMap<_IVariable,_IValue> store, bool pc__tainted, Dafny.IMap<_IVariable,bool> var__map) {
      this.fuel = fuel;
      this.store = store;
      this.pc__tainted = pc__tainted;
      this.var__map = var__map;
    }
    public _ITaintState DowncastClone() {
      if (this is _ITaintState dt) { return dt; }
      return new TaintState(fuel, store, pc__tainted, var__map);
    }
    public override bool Equals(object other) {
      var oth = other as TaintState;
      return oth != null && this.fuel == oth.fuel && object.Equals(this.store, oth.store) && this.pc__tainted == oth.pc__tainted && object.Equals(this.var__map, oth.var__map);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.fuel));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.store));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.pc__tainted));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.var__map));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TaintState.TaintState";
      s += "(";
      s += Dafny.Helpers.ToString(this.fuel);
      s += ", ";
      s += Dafny.Helpers.ToString(this.store);
      s += ", ";
      s += Dafny.Helpers.ToString(this.pc__tainted);
      s += ", ";
      s += Dafny.Helpers.ToString(this.var__map);
      s += ")";
      return s;
    }
    private static readonly _ITaintState theDefault = create(BigInteger.Zero, Dafny.Map<_IVariable, _IValue>.Empty, false, Dafny.Map<_IVariable, bool>.Empty);
    public static _ITaintState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_ITaintState> _TYPE = new Dafny.TypeDescriptor<_ITaintState>(TaintState.Default());
    public static Dafny.TypeDescriptor<_ITaintState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITaintState create(BigInteger fuel, Dafny.IMap<_IVariable,_IValue> store, bool pc__tainted, Dafny.IMap<_IVariable,bool> var__map) {
      return new TaintState(fuel, store, pc__tainted, var__map);
    }
    public bool is_TaintState { get { return true; } }
    public BigInteger dtor_fuel {
      get {
        return this.fuel;
      }
    }
    public Dafny.IMap<_IVariable,_IValue> dtor_store {
      get {
        return this.store;
      }
    }
    public bool dtor_pc__tainted {
      get {
        return this.pc__tainted;
      }
    }
    public Dafny.IMap<_IVariable,bool> dtor_var__map {
      get {
        return this.var__map;
      }
    }
  }

  public interface _ITaintValue {
    bool is_TV { get; }
    bool dtor_tainted { get; }
    _IValue dtor_v { get; }
    _ITaintValue DowncastClone();
  }
  public class TaintValue : _ITaintValue {
    public readonly bool tainted;
    public readonly _IValue v;
    public TaintValue(bool tainted, _IValue v) {
      this.tainted = tainted;
      this.v = v;
    }
    public _ITaintValue DowncastClone() {
      if (this is _ITaintValue dt) { return dt; }
      return new TaintValue(tainted, v);
    }
    public override bool Equals(object other) {
      var oth = other as TaintValue;
      return oth != null && this.tainted == oth.tainted && object.Equals(this.v, oth.v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.tainted));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TaintValue.TV";
      s += "(";
      s += Dafny.Helpers.ToString(this.tainted);
      s += ", ";
      s += Dafny.Helpers.ToString(this.v);
      s += ")";
      return s;
    }
    private static readonly _ITaintValue theDefault = create(false, Value.Default());
    public static _ITaintValue Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_ITaintValue> _TYPE = new Dafny.TypeDescriptor<_ITaintValue>(TaintValue.Default());
    public static Dafny.TypeDescriptor<_ITaintValue> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITaintValue create(bool tainted, _IValue v) {
      return new TaintValue(tainted, v);
    }
    public bool is_TV { get { return true; } }
    public bool dtor_tainted {
      get {
        return this.tainted;
      }
    }
    public _IValue dtor_v {
      get {
        return this.v;
      }
    }
  }

  public interface _ITResult {
    bool is_TTimeout { get; }
    bool is_TLeak { get; }
    bool is_TSuccess { get; }
    _ITaintState dtor_s { get; }
    _ITResult DowncastClone();
  }
  public abstract class TResult : _ITResult {
    public TResult() { }
    private static readonly _ITResult theDefault = create_TTimeout();
    public static _ITResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_ITResult> _TYPE = new Dafny.TypeDescriptor<_ITResult>(TResult.Default());
    public static Dafny.TypeDescriptor<_ITResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITResult create_TTimeout() {
      return new TResult_TTimeout();
    }
    public static _ITResult create_TLeak() {
      return new TResult_TLeak();
    }
    public static _ITResult create_TSuccess(_ITaintState s) {
      return new TResult_TSuccess(s);
    }
    public bool is_TTimeout { get { return this is TResult_TTimeout; } }
    public bool is_TLeak { get { return this is TResult_TLeak; } }
    public bool is_TSuccess { get { return this is TResult_TSuccess; } }
    public _ITaintState dtor_s {
      get {
        var d = this;
        return ((TResult_TSuccess)d).s;
      }
    }
    public abstract _ITResult DowncastClone();
  }
  public class TResult_TTimeout : TResult {
    public TResult_TTimeout() {
    }
    public override _ITResult DowncastClone() {
      if (this is _ITResult dt) { return dt; }
      return new TResult_TTimeout();
    }
    public override bool Equals(object other) {
      var oth = other as TResult_TTimeout;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TResult.TTimeout";
      return s;
    }
  }
  public class TResult_TLeak : TResult {
    public TResult_TLeak() {
    }
    public override _ITResult DowncastClone() {
      if (this is _ITResult dt) { return dt; }
      return new TResult_TLeak();
    }
    public override bool Equals(object other) {
      var oth = other as TResult_TLeak;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TResult.TLeak";
      return s;
    }
  }
  public class TResult_TSuccess : TResult {
    public readonly _ITaintState s;
    public TResult_TSuccess(_ITaintState s) {
      this.s = s;
    }
    public override _ITResult DowncastClone() {
      if (this is _ITResult dt) { return dt; }
      return new TResult_TSuccess(s);
    }
    public override bool Equals(object other) {
      var oth = other as TResult_TSuccess;
      return oth != null && object.Equals(this.s, oth.s);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.s));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "TResult.TSuccess";
      ss += "(";
      ss += Dafny.Helpers.ToString(this.s);
      ss += ")";
      return ss;
    }
  }

  public interface _ISecType {
    bool is_Low { get; }
    bool is_High { get; }
    _ISecType DowncastClone();
  }
  public abstract class SecType : _ISecType {
    public SecType() { }
    private static readonly _ISecType theDefault = create_Low();
    public static _ISecType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_ISecType> _TYPE = new Dafny.TypeDescriptor<_ISecType>(SecType.Default());
    public static Dafny.TypeDescriptor<_ISecType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISecType create_Low() {
      return new SecType_Low();
    }
    public static _ISecType create_High() {
      return new SecType_High();
    }
    public bool is_Low { get { return this is SecType_Low; } }
    public bool is_High { get { return this is SecType_High; } }
    public static System.Collections.Generic.IEnumerable<_ISecType> AllSingletonConstructors {
      get {
        yield return SecType.create_Low();
        yield return SecType.create_High();
      }
    }
    public abstract _ISecType DowncastClone();
  }
  public class SecType_Low : SecType {
    public SecType_Low() {
    }
    public override _ISecType DowncastClone() {
      if (this is _ISecType dt) { return dt; }
      return new SecType_Low();
    }
    public override bool Equals(object other) {
      var oth = other as SecType_Low;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "SecType.Low";
      return s;
    }
  }
  public class SecType_High : SecType {
    public SecType_High() {
    }
    public override _ISecType DowncastClone() {
      if (this is _ISecType dt) { return dt; }
      return new SecType_High();
    }
    public override bool Equals(object other) {
      var oth = other as SecType_High;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "SecType.High";
      return s;
    }
  }

  public interface _IOp {
    bool is_Plus { get; }
    bool is_Sub { get; }
    bool is_Times { get; }
    bool is_Leq { get; }
    bool is_Eq { get; }
    _IOp DowncastClone();
  }
  public abstract class Op : _IOp {
    public Op() { }
    private static readonly _IOp theDefault = create_Plus();
    public static _IOp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IOp> _TYPE = new Dafny.TypeDescriptor<_IOp>(Op.Default());
    public static Dafny.TypeDescriptor<_IOp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOp create_Plus() {
      return new Op_Plus();
    }
    public static _IOp create_Sub() {
      return new Op_Sub();
    }
    public static _IOp create_Times() {
      return new Op_Times();
    }
    public static _IOp create_Leq() {
      return new Op_Leq();
    }
    public static _IOp create_Eq() {
      return new Op_Eq();
    }
    public bool is_Plus { get { return this is Op_Plus; } }
    public bool is_Sub { get { return this is Op_Sub; } }
    public bool is_Times { get { return this is Op_Times; } }
    public bool is_Leq { get { return this is Op_Leq; } }
    public bool is_Eq { get { return this is Op_Eq; } }
    public static System.Collections.Generic.IEnumerable<_IOp> AllSingletonConstructors {
      get {
        yield return Op.create_Plus();
        yield return Op.create_Sub();
        yield return Op.create_Times();
        yield return Op.create_Leq();
        yield return Op.create_Eq();
      }
    }
    public abstract _IOp DowncastClone();
  }
  public class Op_Plus : Op {
    public Op_Plus() {
    }
    public override _IOp DowncastClone() {
      if (this is _IOp dt) { return dt; }
      return new Op_Plus();
    }
    public override bool Equals(object other) {
      var oth = other as Op_Plus;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Op.Plus";
      return s;
    }
  }
  public class Op_Sub : Op {
    public Op_Sub() {
    }
    public override _IOp DowncastClone() {
      if (this is _IOp dt) { return dt; }
      return new Op_Sub();
    }
    public override bool Equals(object other) {
      var oth = other as Op_Sub;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Op.Sub";
      return s;
    }
  }
  public class Op_Times : Op {
    public Op_Times() {
    }
    public override _IOp DowncastClone() {
      if (this is _IOp dt) { return dt; }
      return new Op_Times();
    }
    public override bool Equals(object other) {
      var oth = other as Op_Times;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Op.Times";
      return s;
    }
  }
  public class Op_Leq : Op {
    public Op_Leq() {
    }
    public override _IOp DowncastClone() {
      if (this is _IOp dt) { return dt; }
      return new Op_Leq();
    }
    public override bool Equals(object other) {
      var oth = other as Op_Leq;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Op.Leq";
      return s;
    }
  }
  public class Op_Eq : Op {
    public Op_Eq() {
    }
    public override _IOp DowncastClone() {
      if (this is _IOp dt) { return dt; }
      return new Op_Eq();
    }
    public override bool Equals(object other) {
      var oth = other as Op_Eq;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Op.Eq";
      return s;
    }
  }

  public interface _IVariable {
    bool is_Variable { get; }
    Dafny.ISequence<char> dtor_name { get; }
    _IVariable DowncastClone();
  }
  public class Variable : _IVariable {
    public readonly Dafny.ISequence<char> name;
    public Variable(Dafny.ISequence<char> name) {
      this.name = name;
    }
    public _IVariable DowncastClone() {
      if (this is _IVariable dt) { return dt; }
      return new Variable(name);
    }
    public override bool Equals(object other) {
      var oth = other as Variable;
      return oth != null && object.Equals(this.name, oth.name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Variable.Variable";
      s += "(";
      s += Dafny.Helpers.ToString(this.name);
      s += ")";
      return s;
    }
    private static readonly _IVariable theDefault = create(Dafny.Sequence<char>.Empty);
    public static _IVariable Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IVariable> _TYPE = new Dafny.TypeDescriptor<_IVariable>(Variable.Default());
    public static Dafny.TypeDescriptor<_IVariable> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IVariable create(Dafny.ISequence<char> name) {
      return new Variable(name);
    }
    public bool is_Variable { get { return true; } }
    public Dafny.ISequence<char> dtor_name {
      get {
        return this.name;
      }
    }
  }

  public interface _IExpr {
    bool is_Bool { get; }
    bool is_Int { get; }
    bool is_Var { get; }
    bool is_BinaryOp { get; }
    bool dtor_b { get; }
    BigInteger dtor_i { get; }
    _IVariable dtor_v { get; }
    _IOp dtor_op { get; }
    _IExpr dtor_left { get; }
    _IExpr dtor_right { get; }
    _IExpr DowncastClone();
  }
  public abstract class Expr : _IExpr {
    public Expr() { }
    private static readonly _IExpr theDefault = create_Bool(false);
    public static _IExpr Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IExpr> _TYPE = new Dafny.TypeDescriptor<_IExpr>(Expr.Default());
    public static Dafny.TypeDescriptor<_IExpr> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IExpr create_Bool(bool b) {
      return new Expr_Bool(b);
    }
    public static _IExpr create_Int(BigInteger i) {
      return new Expr_Int(i);
    }
    public static _IExpr create_Var(_IVariable v) {
      return new Expr_Var(v);
    }
    public static _IExpr create_BinaryOp(_IOp op, _IExpr left, _IExpr right) {
      return new Expr_BinaryOp(op, left, right);
    }
    public bool is_Bool { get { return this is Expr_Bool; } }
    public bool is_Int { get { return this is Expr_Int; } }
    public bool is_Var { get { return this is Expr_Var; } }
    public bool is_BinaryOp { get { return this is Expr_BinaryOp; } }
    public bool dtor_b {
      get {
        var d = this;
        return ((Expr_Bool)d).b;
      }
    }
    public BigInteger dtor_i {
      get {
        var d = this;
        return ((Expr_Int)d).i;
      }
    }
    public _IVariable dtor_v {
      get {
        var d = this;
        return ((Expr_Var)d).v;
      }
    }
    public _IOp dtor_op {
      get {
        var d = this;
        return ((Expr_BinaryOp)d).op;
      }
    }
    public _IExpr dtor_left {
      get {
        var d = this;
        return ((Expr_BinaryOp)d).left;
      }
    }
    public _IExpr dtor_right {
      get {
        var d = this;
        return ((Expr_BinaryOp)d).right;
      }
    }
    public abstract _IExpr DowncastClone();
  }
  public class Expr_Bool : Expr {
    public readonly bool b;
    public Expr_Bool(bool b) {
      this.b = b;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Bool(b);
    }
    public override bool Equals(object other) {
      var oth = other as Expr_Bool;
      return oth != null && this.b == oth.b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Expr.Bool";
      s += "(";
      s += Dafny.Helpers.ToString(this.b);
      s += ")";
      return s;
    }
  }
  public class Expr_Int : Expr {
    public readonly BigInteger i;
    public Expr_Int(BigInteger i) {
      this.i = i;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Int(i);
    }
    public override bool Equals(object other) {
      var oth = other as Expr_Int;
      return oth != null && this.i == oth.i;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.i));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Expr.Int";
      s += "(";
      s += Dafny.Helpers.ToString(this.i);
      s += ")";
      return s;
    }
  }
  public class Expr_Var : Expr {
    public readonly _IVariable v;
    public Expr_Var(_IVariable v) {
      this.v = v;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Var(v);
    }
    public override bool Equals(object other) {
      var oth = other as Expr_Var;
      return oth != null && object.Equals(this.v, oth.v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Expr.Var";
      s += "(";
      s += Dafny.Helpers.ToString(this.v);
      s += ")";
      return s;
    }
  }
  public class Expr_BinaryOp : Expr {
    public readonly _IOp op;
    public readonly _IExpr left;
    public readonly _IExpr right;
    public Expr_BinaryOp(_IOp op, _IExpr left, _IExpr right) {
      this.op = op;
      this.left = left;
      this.right = right;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_BinaryOp(op, left, right);
    }
    public override bool Equals(object other) {
      var oth = other as Expr_BinaryOp;
      return oth != null && object.Equals(this.op, oth.op) && object.Equals(this.left, oth.left) && object.Equals(this.right, oth.right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.op));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.right));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Expr.BinaryOp";
      s += "(";
      s += Dafny.Helpers.ToString(this.op);
      s += ", ";
      s += Dafny.Helpers.ToString(this.left);
      s += ", ";
      s += Dafny.Helpers.ToString(this.right);
      s += ")";
      return s;
    }
  }

  public interface _ICommand {
    bool is_Noop { get; }
    bool is_Assign { get; }
    bool is_Concat { get; }
    bool is_IfThenElse { get; }
    bool is_While { get; }
    bool is_PrintS { get; }
    bool is_PrintE { get; }
    bool is_GetInt { get; }
    bool is_GetSecretInt { get; }
    _IVariable dtor_v { get; }
    _IExpr dtor_e { get; }
    _ICommand dtor_c0 { get; }
    _ICommand dtor_c1 { get; }
    _IExpr dtor_cond { get; }
    _ICommand dtor_ifTrue { get; }
    _ICommand dtor_ifFalse { get; }
    _ICommand dtor_body { get; }
    Dafny.ISequence<char> dtor_s { get; }
    _ICommand DowncastClone();
  }
  public abstract class Command : _ICommand {
    public Command() { }
    private static readonly _ICommand theDefault = create_Noop();
    public static _ICommand Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_ICommand> _TYPE = new Dafny.TypeDescriptor<_ICommand>(Command.Default());
    public static Dafny.TypeDescriptor<_ICommand> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICommand create_Noop() {
      return new Command_Noop();
    }
    public static _ICommand create_Assign(_IVariable v, _IExpr e) {
      return new Command_Assign(v, e);
    }
    public static _ICommand create_Concat(_ICommand c0, _ICommand c1) {
      return new Command_Concat(c0, c1);
    }
    public static _ICommand create_IfThenElse(_IExpr cond, _ICommand ifTrue, _ICommand ifFalse) {
      return new Command_IfThenElse(cond, ifTrue, ifFalse);
    }
    public static _ICommand create_While(_IExpr cond, _ICommand body) {
      return new Command_While(cond, body);
    }
    public static _ICommand create_PrintS(Dafny.ISequence<char> s) {
      return new Command_PrintS(s);
    }
    public static _ICommand create_PrintE(_IExpr e) {
      return new Command_PrintE(e);
    }
    public static _ICommand create_GetInt(_IVariable v) {
      return new Command_GetInt(v);
    }
    public static _ICommand create_GetSecretInt(_IVariable v) {
      return new Command_GetSecretInt(v);
    }
    public bool is_Noop { get { return this is Command_Noop; } }
    public bool is_Assign { get { return this is Command_Assign; } }
    public bool is_Concat { get { return this is Command_Concat; } }
    public bool is_IfThenElse { get { return this is Command_IfThenElse; } }
    public bool is_While { get { return this is Command_While; } }
    public bool is_PrintS { get { return this is Command_PrintS; } }
    public bool is_PrintE { get { return this is Command_PrintE; } }
    public bool is_GetInt { get { return this is Command_GetInt; } }
    public bool is_GetSecretInt { get { return this is Command_GetSecretInt; } }
    public _IVariable dtor_v {
      get {
        var d = this;
        if (d is Command_Assign) { return ((Command_Assign)d).v; }
        if (d is Command_GetInt) { return ((Command_GetInt)d).v; }
        return ((Command_GetSecretInt)d).v;
      }
    }
    public _IExpr dtor_e {
      get {
        var d = this;
        if (d is Command_Assign) { return ((Command_Assign)d).e; }
        return ((Command_PrintE)d).e;
      }
    }
    public _ICommand dtor_c0 {
      get {
        var d = this;
        return ((Command_Concat)d).c0;
      }
    }
    public _ICommand dtor_c1 {
      get {
        var d = this;
        return ((Command_Concat)d).c1;
      }
    }
    public _IExpr dtor_cond {
      get {
        var d = this;
        if (d is Command_IfThenElse) { return ((Command_IfThenElse)d).cond; }
        return ((Command_While)d).cond;
      }
    }
    public _ICommand dtor_ifTrue {
      get {
        var d = this;
        return ((Command_IfThenElse)d).ifTrue;
      }
    }
    public _ICommand dtor_ifFalse {
      get {
        var d = this;
        return ((Command_IfThenElse)d).ifFalse;
      }
    }
    public _ICommand dtor_body {
      get {
        var d = this;
        return ((Command_While)d).body;
      }
    }
    public Dafny.ISequence<char> dtor_s {
      get {
        var d = this;
        return ((Command_PrintS)d).s;
      }
    }
    public abstract _ICommand DowncastClone();
  }
  public class Command_Noop : Command {
    public Command_Noop() {
    }
    public override _ICommand DowncastClone() {
      if (this is _ICommand dt) { return dt; }
      return new Command_Noop();
    }
    public override bool Equals(object other) {
      var oth = other as Command_Noop;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Command.Noop";
      return s;
    }
  }
  public class Command_Assign : Command {
    public readonly _IVariable v;
    public readonly _IExpr e;
    public Command_Assign(_IVariable v, _IExpr e) {
      this.v = v;
      this.e = e;
    }
    public override _ICommand DowncastClone() {
      if (this is _ICommand dt) { return dt; }
      return new Command_Assign(v, e);
    }
    public override bool Equals(object other) {
      var oth = other as Command_Assign;
      return oth != null && object.Equals(this.v, oth.v) && object.Equals(this.e, oth.e);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.v));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.e));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Command.Assign";
      s += "(";
      s += Dafny.Helpers.ToString(this.v);
      s += ", ";
      s += Dafny.Helpers.ToString(this.e);
      s += ")";
      return s;
    }
  }
  public class Command_Concat : Command {
    public readonly _ICommand c0;
    public readonly _ICommand c1;
    public Command_Concat(_ICommand c0, _ICommand c1) {
      this.c0 = c0;
      this.c1 = c1;
    }
    public override _ICommand DowncastClone() {
      if (this is _ICommand dt) { return dt; }
      return new Command_Concat(c0, c1);
    }
    public override bool Equals(object other) {
      var oth = other as Command_Concat;
      return oth != null && object.Equals(this.c0, oth.c0) && object.Equals(this.c1, oth.c1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.c0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.c1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Command.Concat";
      s += "(";
      s += Dafny.Helpers.ToString(this.c0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.c1);
      s += ")";
      return s;
    }
  }
  public class Command_IfThenElse : Command {
    public readonly _IExpr cond;
    public readonly _ICommand ifTrue;
    public readonly _ICommand ifFalse;
    public Command_IfThenElse(_IExpr cond, _ICommand ifTrue, _ICommand ifFalse) {
      this.cond = cond;
      this.ifTrue = ifTrue;
      this.ifFalse = ifFalse;
    }
    public override _ICommand DowncastClone() {
      if (this is _ICommand dt) { return dt; }
      return new Command_IfThenElse(cond, ifTrue, ifFalse);
    }
    public override bool Equals(object other) {
      var oth = other as Command_IfThenElse;
      return oth != null && object.Equals(this.cond, oth.cond) && object.Equals(this.ifTrue, oth.ifTrue) && object.Equals(this.ifFalse, oth.ifFalse);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ifTrue));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ifFalse));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Command.IfThenElse";
      s += "(";
      s += Dafny.Helpers.ToString(this.cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ifTrue);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ifFalse);
      s += ")";
      return s;
    }
  }
  public class Command_While : Command {
    public readonly _IExpr cond;
    public readonly _ICommand body;
    public Command_While(_IExpr cond, _ICommand body) {
      this.cond = cond;
      this.body = body;
    }
    public override _ICommand DowncastClone() {
      if (this is _ICommand dt) { return dt; }
      return new Command_While(cond, body);
    }
    public override bool Equals(object other) {
      var oth = other as Command_While;
      return oth != null && object.Equals(this.cond, oth.cond) && object.Equals(this.body, oth.body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Command.While";
      s += "(";
      s += Dafny.Helpers.ToString(this.cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this.body);
      s += ")";
      return s;
    }
  }
  public class Command_PrintS : Command {
    public readonly Dafny.ISequence<char> s;
    public Command_PrintS(Dafny.ISequence<char> s) {
      this.s = s;
    }
    public override _ICommand DowncastClone() {
      if (this is _ICommand dt) { return dt; }
      return new Command_PrintS(s);
    }
    public override bool Equals(object other) {
      var oth = other as Command_PrintS;
      return oth != null && object.Equals(this.s, oth.s);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.s));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "Command.PrintS";
      ss += "(";
      ss += Dafny.Helpers.ToString(this.s);
      ss += ")";
      return ss;
    }
  }
  public class Command_PrintE : Command {
    public readonly _IExpr e;
    public Command_PrintE(_IExpr e) {
      this.e = e;
    }
    public override _ICommand DowncastClone() {
      if (this is _ICommand dt) { return dt; }
      return new Command_PrintE(e);
    }
    public override bool Equals(object other) {
      var oth = other as Command_PrintE;
      return oth != null && object.Equals(this.e, oth.e);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.e));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Command.PrintE";
      s += "(";
      s += Dafny.Helpers.ToString(this.e);
      s += ")";
      return s;
    }
  }
  public class Command_GetInt : Command {
    public readonly _IVariable v;
    public Command_GetInt(_IVariable v) {
      this.v = v;
    }
    public override _ICommand DowncastClone() {
      if (this is _ICommand dt) { return dt; }
      return new Command_GetInt(v);
    }
    public override bool Equals(object other) {
      var oth = other as Command_GetInt;
      return oth != null && object.Equals(this.v, oth.v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Command.GetInt";
      s += "(";
      s += Dafny.Helpers.ToString(this.v);
      s += ")";
      return s;
    }
  }
  public class Command_GetSecretInt : Command {
    public readonly _IVariable v;
    public Command_GetSecretInt(_IVariable v) {
      this.v = v;
    }
    public override _ICommand DowncastClone() {
      if (this is _ICommand dt) { return dt; }
      return new Command_GetSecretInt(v);
    }
    public override bool Equals(object other) {
      var oth = other as Command_GetSecretInt;
      return oth != null && object.Equals(this.v, oth.v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Command.GetSecretInt";
      s += "(";
      s += Dafny.Helpers.ToString(this.v);
      s += ")";
      return s;
    }
  }

  public interface _IValue {
    bool is_B { get; }
    bool is_I { get; }
    bool dtor_b { get; }
    BigInteger dtor_i { get; }
    _IValue DowncastClone();
  }
  public abstract class Value : _IValue {
    public Value() { }
    private static readonly _IValue theDefault = create_B(false);
    public static _IValue Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IValue> _TYPE = new Dafny.TypeDescriptor<_IValue>(Value.Default());
    public static Dafny.TypeDescriptor<_IValue> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IValue create_B(bool b) {
      return new Value_B(b);
    }
    public static _IValue create_I(BigInteger i) {
      return new Value_I(i);
    }
    public bool is_B { get { return this is Value_B; } }
    public bool is_I { get { return this is Value_I; } }
    public bool dtor_b {
      get {
        var d = this;
        return ((Value_B)d).b;
      }
    }
    public BigInteger dtor_i {
      get {
        var d = this;
        return ((Value_I)d).i;
      }
    }
    public abstract _IValue DowncastClone();
  }
  public class Value_B : Value {
    public readonly bool b;
    public Value_B(bool b) {
      this.b = b;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_B(b);
    }
    public override bool Equals(object other) {
      var oth = other as Value_B;
      return oth != null && this.b == oth.b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Value.B";
      s += "(";
      s += Dafny.Helpers.ToString(this.b);
      s += ")";
      return s;
    }
  }
  public class Value_I : Value {
    public readonly BigInteger i;
    public Value_I(BigInteger i) {
      this.i = i;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_I(i);
    }
    public override bool Equals(object other) {
      var oth = other as Value_I;
      return oth != null && this.i == oth.i;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.i));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Value.I";
      s += "(";
      s += Dafny.Helpers.ToString(this.i);
      s += ")";
      return s;
    }
  }

  public interface _IEResult {
    bool is_EFail { get; }
    bool is_ESuccess { get; }
    _IValue dtor_v { get; }
    _IEResult DowncastClone();
  }
  public abstract class EResult : _IEResult {
    public EResult() { }
    private static readonly _IEResult theDefault = create_EFail();
    public static _IEResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IEResult> _TYPE = new Dafny.TypeDescriptor<_IEResult>(EResult.Default());
    public static Dafny.TypeDescriptor<_IEResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEResult create_EFail() {
      return new EResult_EFail();
    }
    public static _IEResult create_ESuccess(_IValue v) {
      return new EResult_ESuccess(v);
    }
    public bool is_EFail { get { return this is EResult_EFail; } }
    public bool is_ESuccess { get { return this is EResult_ESuccess; } }
    public _IValue dtor_v {
      get {
        var d = this;
        return ((EResult_ESuccess)d).v;
      }
    }
    public abstract _IEResult DowncastClone();
  }
  public class EResult_EFail : EResult {
    public EResult_EFail() {
    }
    public override _IEResult DowncastClone() {
      if (this is _IEResult dt) { return dt; }
      return new EResult_EFail();
    }
    public override bool Equals(object other) {
      var oth = other as EResult_EFail;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "EResult.EFail";
      return s;
    }
  }
  public class EResult_ESuccess : EResult {
    public readonly _IValue v;
    public EResult_ESuccess(_IValue v) {
      this.v = v;
    }
    public override _IEResult DowncastClone() {
      if (this is _IEResult dt) { return dt; }
      return new EResult_ESuccess(v);
    }
    public override bool Equals(object other) {
      var oth = other as EResult_ESuccess;
      return oth != null && object.Equals(this.v, oth.v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "EResult.ESuccess";
      s += "(";
      s += Dafny.Helpers.ToString(this.v);
      s += ")";
      return s;
    }
  }

  public interface _IIO {
    bool is_IO { get; }
    _IIO DowncastClone();
  }
  public class IO : _IIO {
    public IO() {
    }
    public _IIO DowncastClone() {
      if (this is _IIO dt) { return dt; }
      return new IO();
    }
    public override bool Equals(object other) {
      var oth = other as IO;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "IO.IO";
      s += "(";
      s += ")";
      return s;
    }
    private static readonly _IIO theDefault = create();
    public static _IIO Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IIO> _TYPE = new Dafny.TypeDescriptor<_IIO>(IO.Default());
    public static Dafny.TypeDescriptor<_IIO> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IIO create() {
      return new IO();
    }
    public bool is_IO { get { return true; } }
  }

  public interface _ICResult {
    bool is_Timeout { get; }
    bool is_Fail { get; }
    bool is_Success { get; }
    Dafny.IMap<_IVariable,_IValue> dtor_s { get; }
    _ICResult DowncastClone();
  }
  public abstract class CResult : _ICResult {
    public CResult() { }
    private static readonly _ICResult theDefault = create_Timeout();
    public static _ICResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_ICResult> _TYPE = new Dafny.TypeDescriptor<_ICResult>(CResult.Default());
    public static Dafny.TypeDescriptor<_ICResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICResult create_Timeout() {
      return new CResult_Timeout();
    }
    public static _ICResult create_Fail() {
      return new CResult_Fail();
    }
    public static _ICResult create_Success(Dafny.IMap<_IVariable,_IValue> s) {
      return new CResult_Success(s);
    }
    public bool is_Timeout { get { return this is CResult_Timeout; } }
    public bool is_Fail { get { return this is CResult_Fail; } }
    public bool is_Success { get { return this is CResult_Success; } }
    public Dafny.IMap<_IVariable,_IValue> dtor_s {
      get {
        var d = this;
        return ((CResult_Success)d).s;
      }
    }
    public abstract _ICResult DowncastClone();
  }
  public class CResult_Timeout : CResult {
    public CResult_Timeout() {
    }
    public override _ICResult DowncastClone() {
      if (this is _ICResult dt) { return dt; }
      return new CResult_Timeout();
    }
    public override bool Equals(object other) {
      var oth = other as CResult_Timeout;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "CResult.Timeout";
      return s;
    }
  }
  public class CResult_Fail : CResult {
    public CResult_Fail() {
    }
    public override _ICResult DowncastClone() {
      if (this is _ICResult dt) { return dt; }
      return new CResult_Fail();
    }
    public override bool Equals(object other) {
      var oth = other as CResult_Fail;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "CResult.Fail";
      return s;
    }
  }
  public class CResult_Success : CResult {
    public readonly Dafny.IMap<_IVariable,_IValue> s;
    public CResult_Success(Dafny.IMap<_IVariable,_IValue> s) {
      this.s = s;
    }
    public override _ICResult DowncastClone() {
      if (this is _ICResult dt) { return dt; }
      return new CResult_Success(s);
    }
    public override bool Equals(object other) {
      var oth = other as CResult_Success;
      return oth != null && object.Equals(this.s, oth.s);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.s));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "CResult.Success";
      ss += "(";
      ss += Dafny.Helpers.ToString(this.s);
      ss += ")";
      return ss;
    }
  }

  public interface _IState {
    bool is_State { get; }
    BigInteger dtor_fuel { get; }
    Dafny.IMap<_IVariable,_IValue> dtor_store { get; }
    _IState DowncastClone();
  }
  public class State : _IState {
    public readonly BigInteger fuel;
    public readonly Dafny.IMap<_IVariable,_IValue> store;
    public State(BigInteger fuel, Dafny.IMap<_IVariable,_IValue> store) {
      this.fuel = fuel;
      this.store = store;
    }
    public _IState DowncastClone() {
      if (this is _IState dt) { return dt; }
      return new State(fuel, store);
    }
    public override bool Equals(object other) {
      var oth = other as State;
      return oth != null && this.fuel == oth.fuel && object.Equals(this.store, oth.store);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.fuel));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.store));
      return (int) hash;
    }
    public override string ToString() {
      string s = "State.State";
      s += "(";
      s += Dafny.Helpers.ToString(this.fuel);
      s += ", ";
      s += Dafny.Helpers.ToString(this.store);
      s += ")";
      return s;
    }
    private static readonly _IState theDefault = create(BigInteger.Zero, Dafny.Map<_IVariable, _IValue>.Empty);
    public static _IState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IState> _TYPE = new Dafny.TypeDescriptor<_IState>(State.Default());
    public static Dafny.TypeDescriptor<_IState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IState create(BigInteger fuel, Dafny.IMap<_IVariable,_IValue> store) {
      return new State(fuel, store);
    }
    public bool is_State { get { return true; } }
    public BigInteger dtor_fuel {
      get {
        return this.fuel;
      }
    }
    public Dafny.IMap<_IVariable,_IValue> dtor_store {
      get {
        return this.store;
      }
    }
  }

  public interface _IType {
    bool is_TInt { get; }
    bool is_TBool { get; }
    _IType DowncastClone();
  }
  public abstract class Type : _IType {
    public Type() { }
    private static readonly _IType theDefault = create_TInt();
    public static _IType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_IType> _TYPE = new Dafny.TypeDescriptor<_IType>(Type.Default());
    public static Dafny.TypeDescriptor<_IType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IType create_TInt() {
      return new Type_TInt();
    }
    public static _IType create_TBool() {
      return new Type_TBool();
    }
    public bool is_TInt { get { return this is Type_TInt; } }
    public bool is_TBool { get { return this is Type_TBool; } }
    public static System.Collections.Generic.IEnumerable<_IType> AllSingletonConstructors {
      get {
        yield return Type.create_TInt();
        yield return Type.create_TBool();
      }
    }
    public abstract _IType DowncastClone();
  }
  public class Type_TInt : Type {
    public Type_TInt() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TInt();
    }
    public override bool Equals(object other) {
      var oth = other as Type_TInt;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Type.TInt";
      return s;
    }
  }
  public class Type_TBool : Type {
    public Type_TBool() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TBool();
    }
    public override bool Equals(object other) {
      var oth = other as Type_TBool;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Type.TBool";
      return s;
    }
  }
} // end of namespace _module
