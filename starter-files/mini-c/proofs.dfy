include "def.dfy"

// Helper Lemma #1:
//   Evaluating a well-typed expression using a well-typed store
//   will always succeed
lemma WellTypedExprSuccess(d:Declarations, s:Store, e:Expr, t:Type) 
    requires StoreWellTyped(d, s)
    requires ExprHasType(d, e, t)
    ensures  EvalExpr(e, s).ESuccess?
    // As a further sanity check, you may want confirm that Dafny proves these intermediate results:
    // ensures t.TInt? ==> EvalExpr(e, s).v.I?
    // ensures t.TBool? ==> EvalExpr(e, s).v.B?
{    
    // Dafny should prove this automatically, if your type
    // checking rules are correct
}

// Helper Lemma #2:
//   Evaluating a well-typed command using a well-typed store
//   will either time out (e.g., imagine a well-typed infinite loop),
//   or evaluated successfully and produce a well-typed store
lemma WellTypedCommandSuccess(d:Declarations, s:State, c:Command) 
    requires StoreWellTyped(d, s.store)
    requires CommandWellTyped(d, c)    
    decreases s.fuel, c
    ensures  EvalCommand(s, c).Timeout? || 
             (EvalCommand(s, c).Success?  && StoreWellTyped(d, EvalCommand(s, c).s))
{
    // DONOT remove the code marker 
    // DONOT modify the code beyond the code markers 
    //####CodeMarker1Begin####
    if s.fuel > 0 {
        match c {
            case Noop => // Dafny automatically proves this case                

            case Assign(v, e) => 
                WellTypedExprSuccess(d, s.store, e, d[v]);

            case Concat(c0, c1) => 
                WellTypedCommandSuccess(d, s, c0);
                if EvalCommand(s, c0).Success? {
                    var Success(store', io') := EvalCommand(s, c0);
                    WellTypedCommandSuccess(d, State(s.fuel, store', io'), c1);
                }

            case IfThenElse(cond, ifTrue, ifFalse) => 
                // TODO: Update this case, so the proof goes through
                WellTypedExprSuccess(d, s.store, cond, TBool); 
                WellTypedCommandSuccess(d, s, ifTrue);
                WellTypedCommandSuccess(d, s, ifFalse);

            case While(cond, body) => 
                WellTypedExprSuccess(d, s.store, cond, TBool); 
                WellTypedCommandSuccess(d, State(s.fuel - 1, s.store, s.io), Concat(body, c));

            case PrintS(str) =>
                // TODO: Update this case, so the proof goes through

            case PrintE(e) =>  
                //WellTypedExprSuccess(d, s.store, e, TBool); 
                // TODO: Update this case, so the proof goes through
                {match e
                    case Bool(_) =>  WellTypedExprSuccess(d, s.store, e, TBool);
                    case Int(_) => WellTypedExprSuccess(d, s.store, e, TInt);
                    case Var(v) =>
                    case BinaryOp(op, lhs, rhs) => 
                        WellTypedExprSuccess(d, s.store, lhs, TInt);
                        WellTypedExprSuccess(d, s.store, rhs, TInt);

                }
                    //WellTypedExprSuccess(d, s.store, e, TBool);
                //var value:= WellTypedExprSuccess(d, s.store, e, TBool)|| WellTypedExprSuccess(d, s.store, e, TInt);
                

            case GetInt(variable) =>  // Dafny automatically proves this case

            case GetSecretInt(variable) => 
                // TODO: Update this case, so the proof goes through
        }
    }
    //####CodeMarker1End####
}

// Our top level type-safety theorem:
//   If evaluating a well-typed command using a well-typed store
//   does not time out, then it must succeed (i.e., it doesn't fail),
//   and it produces a well-typed store
lemma TypeSafety(d:Declarations, s:State, io:IO, c:Command)
    requires StoreWellTyped(d, s.store)
    requires CommandWellTyped(d, c)   
    requires !EvalCommand(s, c).Timeout?
    ensures  EvalCommand(s, c).Success? && 
             StoreWellTyped(d, EvalCommand(s, c).s)
{
    // Invoke our helper lemma (#2)
    WellTypedCommandSuccess(d, s, c);
}
