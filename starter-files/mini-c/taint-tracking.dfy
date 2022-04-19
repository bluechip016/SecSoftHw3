include "proofs.dfy"

//////////////////////////////////////////////////////////////////
//
//  Taint Tracking for Exressions
//
//////////////////////////////////////////////////////////////////

// TaintState is like State, but it also keeps track of whether the
// Program Counter (PC) has been tainted, as well as the taint
// status of each variable
type VarTaintMap = map<Variable, bool>
datatype TaintState = TaintState(fuel:nat, store:Store, ghost io:IO, pc_tainted:bool, var_map:VarTaintMap)

// Converts a TaintState back to a normal State
function ToState(s:TaintState) : State {
    State(s.fuel, s.store, s.io)
}

predicate AllVariablesTracked(s:TaintState) 
{
    forall v :: v in s.store ==> v in s.var_map    
}

// Semantics of (tainted) expression evaluation,
// which returns both a value _and_ whether that value is tainted
datatype TaintValue = TV(tainted:bool, v:Value)
function method EvalExprTaint(d:Declarations, s:TaintState, e:Expr, t:Type) : (tv:TaintValue)
    requires ExprHasType(d, e, t)
    requires StoreWellTyped(d, s.store)
    requires AllVariablesTracked(s)
    ensures  EvalExpr(e, s.store).ESuccess?;
    ensures  tv.v == EvalExpr(e, s.store).v
{
    // DONOT remove the code marker 
    // DONOT modify the code beyond the code markers 
    //####CodeMarker1Begin#### 
    // Use the fact that the expression is well typed to eliminate the need to handle error cases
    WellTypedExprSuccess(d, s.store, e, t);
    match e        
        case Bool(b) => TV(false, B(b))     // Constants are not tainted
        case Int(i)  => TV(false, I(i))     // Constants are not tainted
        case Var(v)  => TV(s.var_map[v], s.store[v])
        case BinaryOp(op, lhs, rhs) => 
            // TODO: Fill this case in properly
           var lhs:=EvalExprTaint(d,s,lhs,TInt);
           var rhs:=EvalExprTaint(d,s,rhs,TInt);          
           if (  lhs.tainted==true   ||  rhs.tainted==true  ) then
               match op                    
                     case Plus  => TV(true,I(lhs.v.i +  rhs.v.i)) 
                    case Sub   => TV(true,I(lhs.v.i -  rhs.v.i)) 
                    case Times => TV(true,I(lhs.v.i *  rhs.v.i)) 
                    case Leq   => TV(true,B(lhs.v.i <=rhs.v.i))
                    case Eq    => TV(true,B(lhs.v.i == rhs.v.i))
           else
               match op                    
                    case Plus  => TV(false,I(lhs.v.i +  rhs.v.i)) 
                    case Sub   => TV(false,I(lhs.v.i -  rhs.v.i)) 
                    case Times => TV(false,I(lhs.v.i *  rhs.v.i)) 
                    case Leq   => TV(false,B(lhs.v.i <= rhs.v.i))
                    case Eq    => TV(false,B(lhs.v.i == rhs.v.i))
    //####CodeMarker1End####
}

lemma TaintExamplesExpr(io: IO) {
    // Same command as before
    var x := Variable("x");
    var y := Variable("y");
    var e := BinaryOp(Times, Var(x), Var(y));

    var d := map[x := TInt, y := TInt];

    var store := map[x := I(2), y := I(3)];

    var taintMap := map[x := false, y := false];
    var taintState := TaintState(1, store, io, false, taintMap);
    
    //Example: No taint
    assert !EvalExprTaint(d, taintState, e, TInt).tainted;

    //Example: lhs is tainted
    taintMap := map[x := true, y := false];
    taintState := TaintState(1, store, io, false, taintMap);
    assert EvalExprTaint(d, taintState, e, TInt).tainted;
}

//////////////////////////////////////////////////////////////////
//
//  Taint Tracking for Commands
//
//////////////////////////////////////////////////////////////////

// The taint engine can time out, detect a leak, or successfully execute the command
datatype TResult = TTimeout | TLeak | TSuccess(s:TaintState)

/*** Define some helper functions as convenient shortcuts ***/

// Update the var_map within taint_state, so that v now maps to taint
function method UpdateVarTaint(s:TaintState, v:Variable, taint:bool) : TaintState {
    s.(var_map := s.var_map[v := taint])
}

// Update the store within taint_state, so that v now maps to val
function method UpdateVarVal(s:TaintState, v:Variable, val:Value) : TaintState {
    s.(store := s.store[v := val])
}

// Update the taint setting for the PC within taint_state
function method UpdatePCTaint(s:TaintState, taint:bool) : TaintState {
    s.(pc_tainted := taint)
}

function method {:extern} PrintErr(s:string) : ()

//
// Our taint-tracking engine
//
function method EvalCommandTaint(d:Declarations, s:TaintState, c:Command) : (t:TResult)
    // Given a well-typed command and store, and a TaintState that is properly populated
    requires CommandWellTyped(d, c)
    requires StoreWellTyped(d, s.store)
    requires AllVariablesTracked(s)
    decreases s.fuel, c
    // We ensure that when execution succeeds, the TaintState is still properly populated,
    // the store is still well typed, and our fuel doesn't increase (needed to prove termination)
    ensures  t.TSuccess? ==> AllVariablesTracked(t.s) && StoreWellTyped(d, t.s.store) && t.s.fuel <= s.fuel
    // We also ensure that our taint tracker obeys the original semantics for commands
    ensures  var r := EvalCommand(ToState(s), c);
             t.TSuccess? ==> r.Success? && r.s == t.s.store && r.io == t.s.io
{  
    //####CodeMarker2Begin####
    // Use the fact that the command is well typed to eliminate the need to handle error cases
    WellTypedCommandSuccess(d, ToState(s), c);
    if s.fuel == 0 then TTimeout  // We ran too long
    else
    match c
        case Noop =>  TSuccess(s)

        case Assign(variable, e) => 
            if !s.var_map[variable] && s.pc_tainted then
                // Assigning to an untainted variable while the PC is tainted
                // can leak information (since later use of that variable can cause execution to fail)
                TLeak   
            else
                // Evaluate the expression and calculate its taint
                var TV(taint, value) := EvalExprTaint(d, s, e, d[variable]);
                // The variable will be tainted if the expression is tainted _or_ the PC is tainted
                // In the latter case, we reached this assignment by branching on a tainted value
                var new_taint := taint || s.pc_tainted;
                // Update the taint value in our VarTaintMap
                var new_s := UpdateVarTaint(s, variable, new_taint);
                // Update the store
                var s' := UpdateVarVal(new_s, variable, value);
                TSuccess(s')

        case Concat(c0, c1) =>
            // First evaluate the left-hand side (c0)
            var result0 := EvalCommandTaint(d, s, c0);
            (match result0
                // If c0 times out or fails, we do the same
                case TTimeout => TTimeout
                case TLeak => TLeak
                case TSuccess(s') =>
                    // If c0 succeeds, then we evaluate the right-hand side (c1)
                    WellTypedCommandSuccess(d, ToState(s), c0);
                    EvalCommandTaint(d, s'.(fuel := s.fuel), c1)
            )

        case IfThenElse(cond, ifTrue, ifFalse) =>
            // TODO: Fill this case in properly
            //TSuccess(s)
            var TV(taint, B(b)) := EvalExprTaint(d, s, cond, TBool);
            if b then
                var new_s := if taint then UpdatePCTaint(s, true) else s; 
                var result := EvalCommandTaint(d, new_s, ifTrue);
                (match result
                    case TTimeout => TTimeout
                    case TLeak => TLeak
                    case TSuccess(s') =>    
                        // Now that we've executed the loop, restore the PC's taint
                        // to its previous value
                        TSuccess(UpdatePCTaint(s', s.pc_tainted)))
            else     
                var new_s := if taint then UpdatePCTaint(s, true) else s; 
                var result := EvalCommandTaint(d, new_s, ifFalse);
                (match result
                    case TTimeout => TTimeout
                    case TLeak => TLeak
                    case TSuccess(s') =>    
                        // Now that we've executed the loop, restore the PC's taint
                        // to its previous value
                        TSuccess(UpdatePCTaint(s', s.pc_tainted)))

        case While(cond, body) =>
            // First evaluate the conditional expression
            var TV(taint, B(b)) := EvalExprTaint(d, s, cond, TBool);
            if !b then TSuccess(s)   // The while loop is complete                        
            else // Otherwise, execute the body, and then re-evaluate the while loop code (c)
                // If the conditional is tainted, then we must treat the PC as tainted         
                var new_s := if taint then UpdatePCTaint(s, true) else s; 
                var result := EvalCommandTaint(d, new_s.(fuel := s.fuel - 1), Concat(body, c));
                (match result
                    // If the loop times out for fails, we do the same
                    case TTimeout => TTimeout
                    case TLeak => TLeak
                    case TSuccess(s') =>    
                        // Now that we've executed the loop, restore the PC's taint
                        // to its previous value
                        TSuccess(UpdatePCTaint(s', s.pc_tainted)))

        case PrintS(str) =>
            // TODO: Fill this case in properly
            //TSuccess(s)
            if s.pc_tainted then
                TLeak
            else
                var io':=PrintString(str,s.io);
                TSuccess(s.(io:=io'))

        case PrintE(e) => 
            // TODO: Fill this case in properly
            if s.pc_tainted then
                TLeak
            else
                var value:=EvalExpr(e,s.store);
                (
                match value
                case EFail => TSuccess(s)
                case ESuccess(I(i)) =>
                     var str:= Int2String(i);
                     var io':=PrintString(str,s.io);
                    TSuccess(s.(io:=io'))
                case ESuccess(B(b)) => 
                    var str:= Bool2String(b);
                    var io':=PrintString(str,s.io);
                   TSuccess(s.(io:=io'))
            )


                
        case GetInt(variable) =>
            if s.pc_tainted then
                // We're in a tainted state, so we can't allow any interactions with the public world
                TLeak               
            else
                // Get an integer from the outside world, which gives us an updated IO record
                // Since this is a public input, we don't allow it to depend on the secrets
                // we've received so far, so we temporarily remove them from the IO
                var (i, io') := ReadInt(s.io.(in_secret := []));
                // Update the store with the integer we received
                var new_store := s.store[variable := I(i)];
                // Update the taint state to indicate that this variable is now not tainted
                var new_s := UpdateVarTaint(s, variable, false);
                TSuccess(TaintState(s.fuel, new_store,  io'.(in_secret := s.io.in_secret), new_s.pc_tainted, new_s.var_map))

        case GetSecretInt(variable) =>
            if !s.var_map[variable] && s.pc_tainted then
                // Assigning to a low variable while the PC is tainted
                // can leak information (since later use of that variable can cause it to fail)
                TLeak   
            else
                // Get a secret integer from the outside world, 
                // which gives us an updated IO record
                var (i, io') := ReadSecretInt(s.io);
                // Update the store with the integer we received
                var new_store := s.store[variable := I(i)];
                // Update the taint state to indicate that this variable is now tainted
                var new_s := UpdateVarTaint(s, variable, true);         
                TSuccess(TaintState(s.fuel, new_store,  io', new_s.pc_tainted, new_s.var_map))
    //####CodeMarker2End####
}

lemma TaintExamplesCommand(io: IO) {
    var x := Variable("x");
    var y := Variable("y");
    var cond := BinaryOp(Eq, Var(x), Int(1));
    var ifTrue := Assign(y, Int(1));
    var ifFalse := Assign(y, Int(0));
    var ite := IfThenElse(cond, ifTrue, ifFalse);
    var command:Command;

    var d := map[x := TInt, y := TInt];

    var store := map[x := I(1), y := I(3)];

    var taintMap := map[x := false, y := false];
    var taintState := TaintState(1, store, io, false, taintMap);

    //ifThenElse
    //Example: Condition is tainted and true
    taintMap := map[x := true, y := false];
    taintState := TaintState(1, store, io, false, taintMap);
    assert EvalExprTaint(d, taintState, cond, TBool).tainted;
    assert EvalCommandTaint(d, taintState, ite).TLeak?;

    //Example: Condition is not tainted. pc_tainted is true
    taintMap := map[x := false, y := false];
    taintState := TaintState(1, store, io, true, taintMap);
    assert EvalCommandTaint(d, taintState, ite).TLeak?;
    
    //PrintS
    //Example: pc_tainted is true
    command := PrintS("Hello");
    d := map[];
    store := map[];
    taintMap := map[]; 
    taintState := TaintState(1, store, io, true, taintMap);
    assert EvalCommandTaint(d, taintState, command).TLeak?;
}

//////////////////////////////////////////////////////////////////
//
//  Proof That Taint Tracking Ensures Non-Interference
//
//////////////////////////////////////////////////////////////////

/*** First define some helper functions to abbreviate long expressions ***/

// All variables declared in d as type t have the same value in s0 and s1
predicate UntaintedVarsAgree(d:Declarations, s0:TaintState, s1:TaintState) 
    requires AllVariablesTracked(s0) && AllVariablesTracked(s1)
{
    forall variable :: 
        variable in d ==> 
            variable in s0.store 
         && variable in s1.store
         && (s0.var_map[variable] <==> s1.var_map[variable])
         && (!s0.var_map[variable] ==> s0.store[variable] == s1.store[variable])
}

/*** Now define some helper lemmas ***/

// Helper lemma 1
lemma NonInterfenceExpr(d:Declarations, s0:TaintState, s1:TaintState, e:Expr, t:Type)
    // If a well-typed expression (e) is evaluated against two well-typed stores,
    // and the untainted variables have the same value in both stores,
    requires ExprHasType(d, e, t)
    requires StoreWellTyped(d, s0.store) && StoreWellTyped(d, s1.store)
    requires AllVariablesTracked(s0) && AllVariablesTracked(s1)    
    requires UntaintedVarsAgree(d, s0, s1)
    // Then both evaluations agree on the tainted status of the result
    ensures  EvalExprTaint(d, s0, e, t).tainted <==> EvalExprTaint(d, s1, e, t).tainted
    // And if the result is untainted, then both evaluations agree on the value
    ensures  !EvalExprTaint(d, s0, e, t).tainted ==>
                EvalExprTaint(d, s0, e, t).v == EvalExprTaint(d, s1, e, t).v
{
    //####CodeMarker3Begin####
    match e {
        case Bool(b) => 
        case Int(i)  => 
        case Var(v)  => 
        case BinaryOp(op, lhs, rhs) =>
            NonInterfenceExpr(d,s0,s1,lhs,TInt);
            NonInterfenceExpr(d,s0,s1,rhs,TInt);

        // TODO: Update this case, so the proof goes through 
    }
    //####CodeMarker3End####
}

// Helper lemma 2
lemma TaintedPcPreservesLowVarsPubIO(d:Declarations, s:TaintState, c:Command, r:TResult)
    // If we evaluate a well-typed command against a well defined TaintState
    // and the original PC is tainted, and the evaluationed is successful
    requires CommandWellTyped(d, c) && StoreWellTyped(d, s.store)
    requires AllVariablesTracked(s)
    requires s.pc_tainted;
    requires EvalCommandTaint(d, s, c) == r
    requires r.TSuccess?    
    decreases s.fuel, c
    // Then the resulting taint state is still well-formed
    ensures  AllVariablesTracked(r.s)
    // The untainted variables in the new state have the same value as in the old state
    ensures  UntaintedVarsAgree(d, s, r.s)
    // The PC is still tainted
    ensures  r.s.pc_tainted
    // And the public inputs and the output have stayed the same
    ensures  r.s.io.in_public == s.io.in_public
    ensures  r.s.io.output == s.io.output
{
    //####CodeMarker4Begin####
    match c {
        case Noop => // automatic 

        case Assign(variable, e) => // automatic 

        case Concat(c0, c1) =>
            var result0 := EvalCommandTaint(d, s, c0);            
            TaintedPcPreservesLowVarsPubIO(d, s, c0, result0);
            TaintedPcPreservesLowVarsPubIO(d, result0.s.(fuel := s.fuel), c1, r);

        case IfThenElse(cond, ifTrue, ifFalse) =>
            // TODO: Fill this case in properly
             var TV(taint, B(b)) := EvalExprTaint(d, s, cond, TBool);
            if !b {
                var result := EvalCommandTaint(d, s, ifFalse);
                TaintedPcPreservesLowVarsPubIO(d, s, ifFalse, result);
            } else {
                var result := EvalCommandTaint(d, s, ifTrue);
                TaintedPcPreservesLowVarsPubIO(d, s, ifTrue, result);
            }

        case While(cond, body) =>             
            var TV(taint, B(b)) := EvalExprTaint(d, s, cond, TBool);
            if !b {
            } else {
                var s' := s.(fuel := s.fuel - 1);
                var result := EvalCommandTaint(d, s', Concat(body, c));
                TaintedPcPreservesLowVarsPubIO(d, s', Concat(body, c), result);
            }
        case PrintS(str) => // automatic 
        case PrintE(e) => // automatic
        case GetInt(variable) => // automatic 
        case GetSecretInt(variable) => // automatic
    }
    //####CodeMarker4End#### 
}


// This is where most of the work of proving non-interference happens.
// It is an inductive argument over the structure of the program (c).
lemma NonInterferenceInternal(d:Declarations, 
                              s0:TaintState, s1:TaintState,
                              c:Command,                                                              
                              r0:TResult, r1:TResult) 
    // 0) The command and stores are well typed
    requires CommandWellTyped(d, c) && StoreWellTyped(d, s0.store) && StoreWellTyped(d, s1.store)

    // 1) The stores and the taint_state talk about the same variables
    requires AllVariablesTracked(s0) && AllVariablesTracked(s1)

    // 2) Initial IO states agree on the public inputs and the outputs
    requires s0.io.in_public == s1.io.in_public && s0.io.output == s1.io.output

    // 3) The initial stores agree on the values of all untainted variables
    requires UntaintedVarsAgree(d, s0, s1)

    // 4) The inital states agree whether the PC is tainted
    requires s0.pc_tainted == s1.pc_tainted

    // 5) The results passed in (r0 and r1) match the actual result of evaluating the command, 
    //   starting from s0 and from s1 respectively
    requires EvalCommandTaint(d, s0, c) == r0
    requires EvalCommandTaint(d, s1, c) == r1

    // 6) Evaluation was successful
    requires r0.TSuccess?
    requires r1.TSuccess?

    decreases s0.fuel, s1.fuel, c

    // Some additional invariants we'll need for our proof:
    //   a) The stores remain well-typed
    ensures StoreWellTyped(d, r0.s.store) && StoreWellTyped(d, r1.s.store)

    //   b) After we execute the command, all variables are still tracked
    ensures AllVariablesTracked(r0.s) && AllVariablesTracked(r1.s)

    //   c) After we execute the command, the value of the untainted variables stays the same in both stores
    ensures UntaintedVarsAgree(d, r0.s, r1.s)

    //   d) The results agree on whether the PC is tainted
    ensures r0.s.pc_tainted == r1.s.pc_tainted

    //   e) The public inputs we receive are the same in both executions
    ensures r0.s.io.in_public == r1.s.io.in_public

    // Conclusion: The output of both executions are identical
    ensures  r0.s.io.output == r1.s.io.output
{
    //####CodeMarker5Begin####
    match c {
        case Noop =>

        case Assign(variable, e) =>
            // Prove that the two expression evaluations will agree
            // on the resulting taint status, if that status is untainted,
            // then they agree on the value too
            NonInterfenceExpr(d, s0, s1, e, d[variable]);

        case Concat(c0, c1) =>
            var result0 := EvalCommandTaint(d, s0, c0);
            var result1 := EvalCommandTaint(d, s1, c0);
            // Apply the inductive hypothesis to each sub-command
            NonInterferenceInternal(d, s0, s1, c0, result0, result1);
            NonInterferenceInternal(d, result0.s.(fuel := s0.fuel), result1.s.(fuel := s1.fuel), c1, r0, r1);

        case IfThenElse(cond, ifTrue, ifFalse) => 
            NonInterfenceExpr(d, s0, s1, cond, TBool);

            var TV(taint0, B(b0)) := EvalExprTaint(d, s0, cond, TBool);
            var TV(taint1, B(b1)) := EvalExprTaint(d, s1, cond, TBool);

            // If the conditional is tainted, then we must treat the PC as tainted         
            var new_s0 := if taint0 then UpdatePCTaint(s0, true) else s0;
            var new_s1 := if taint1 then UpdatePCTaint(s1, true) else s1;

            if !taint0 {
                // TODO: Fill this case in properly
                var result10 := EvalCommandTaint(d, new_s0, ifTrue);
                var result00 := EvalCommandTaint(d, new_s0, ifFalse);
                var result11 := EvalCommandTaint(d, new_s1, ifTrue);
                var result01 := EvalCommandTaint(d, new_s1, ifFalse);
                assert b0 == b1;
                if !b0{
                    NonInterferenceInternal(d, new_s0, s1, ifFalse, result00, result01);}
                else{
                    NonInterferenceInternal(d, new_s0, s1, ifTrue, result10, result11);}
            } else {
                var result10 := EvalCommandTaint(d, new_s0, ifTrue);
                var result00 := EvalCommandTaint(d, new_s0, ifFalse);
                var result11 := EvalCommandTaint(d, new_s1, ifTrue);
                var result01 := EvalCommandTaint(d, new_s1, ifFalse);
                if b0{
                    TaintedPcPreservesLowVarsPubIO(d, new_s0, ifTrue, result10);
                }else{
                    TaintedPcPreservesLowVarsPubIO(d, new_s0, ifFalse, result00);
                }
                if b1{
                    TaintedPcPreservesLowVarsPubIO(d, new_s1, ifTrue, result11);
                }else{
                    TaintedPcPreservesLowVarsPubIO(d, new_s1, ifFalse, result01);
                }
                
                // TODO: Fill this case in properly
            }
        case While(cond, body) => 
            NonInterfenceExpr(d, s0, s1, cond, TBool);

            var TV(taint0, B(b0)) := EvalExprTaint(d, s0, cond, TBool);
            var TV(taint1, B(b1)) := EvalExprTaint(d, s1, cond, TBool);

            // If the conditional is tainted, then we must treat the PC as tainted
            var new_s0 := if taint0 then UpdatePCTaint(s0, true) else s0; 
            var new_s1 := if taint1 then UpdatePCTaint(s1, true) else s1;

            // Decrement the fuel
            var s0' := new_s0.(fuel := new_s0.fuel - 1);
            var s1' := new_s1.(fuel := new_s1.fuel - 1);

            // Calculate what the result will be if we have to iterate the loop again
            var result0 := EvalCommandTaint(d, s0', Concat(body, c));
            var result1 := EvalCommandTaint(d, s1', Concat(body, c));

            if !taint0 {
                assert b0 == b1; // Both executions agree on whether to terminate the loop
                if !b0 {
                    // Easy case: Both loops terminate
                } else {          
                    // Harder case: Both loops continue.  We invoke the induction hypothesis.          
                    NonInterferenceInternal(d, s0', s1', Concat(body, c), result0, result1);
                }            
            } else {
                // The executions may not agree on whether to terminate the loop
                if b0 {
                    // If execution 0 decides to execute the loop, show that it still
                    // preserves the untainted variables and the public IO
                    TaintedPcPreservesLowVarsPubIO(d, s0', Concat(body, c), result0);
                }
                if b1 {
                    // If execution 1 decides to execute the loop, show that it still
                    // preserves the untainted variables and the public IO
                    TaintedPcPreservesLowVarsPubIO(d, s1', Concat(body, c), result1);                    
                }          
            }
        case PrintS(str) => // automatic
        case PrintE(e) => 
            // TODO: Fill this case in properly

        case GetInt(variable) => // automatic
        case GetSecretInt(variable) => // automatic
    }
    //####CodeMarker5End####  
}

// This is the top-level non-interference proof. 
// It says that our taint-tracking engine really
// does enforce non-interference: No matter what
// the tainted variables are initially set to, 
// and no matter what Secret integers are read,
// the public output is always the same.

// The signature for this lemma is all a human
// reviewer would need to read.  All of the proof
// above is mechanically checked.
lemma NonInterference(d:Declarations, s0:TaintState, s1:TaintState, c:Command, r0:TResult, r1:TResult) 
    // 0) The command and stores are well typed
    requires CommandWellTyped(d, c) && StoreWellTyped(d, s0.store) && StoreWellTyped(d, s1.store)

    // 1) The stores and the taint_state talk about the same variables
    requires AllVariablesTracked(s0) && AllVariablesTracked(s1)

    // 2) Initial IO states agree on the public inputs and the outputs
    requires s0.io.in_public == s1.io.in_public && s0.io.output == s1.io.output

    // 3) The initial stores agree on the values of all untainted variables
    requires UntaintedVarsAgree(d, s0, s1)

    // 4) The inital states agree whether the PC is tainted
    requires s0.pc_tainted == s1.pc_tainted

    // 5) The results passed in (r0 and r1) match the actual result of evaluating the command, 
    //    starting from s0 and from s1 respectively
    requires EvalCommandTaint(d, s0, c) == r0
    requires EvalCommandTaint(d, s1, c) == r1

    // 6) Evaluation was successful
    requires r0.TSuccess?
    requires r1.TSuccess?

    // Conclusion: The output of both executions are identical, 
    // even though initially the tainted variables in the stores may differ,
    // and the two executions might read different secret integers
    ensures  r0.s.io.output == r1.s.io.output
{
    NonInterferenceInternal(d, s0, s1, c, r0, r1);
}
