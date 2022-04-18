include "def.dfy"

//////////////////////////////////////////////////////////////////
//
//  _Security_ Typing Rules
//
//////////////////////////////////////////////////////////////////

// For simplicity, we only have two levels in our security lattice,
// but this could be extended with additional types (e.g., TopSecret)
datatype SecType = Low | High

// Define the relationship between Low and High
predicate leq(t0:SecType, t1:SecType) {
    t0 == t1 ||
    (t0.Low? && t1.High?)
}

// The program's declarations establish which security type each variable has
type SecDeclarations = map<Variable,SecType>

// Define what it means for an expression to be well typed 
// with respect to a particular security level.
// When this predicate is true, that means that with 
// respect to the declarations (d), expression e has type t
// Recall: "predicate" is just a function that returns bool
predicate method ExprHasSecType(d:SecDeclarations, e:Expr, t:SecType) { 
    // DONOT remove the code marker 
    // DONOT modify the code beyond the code markers 
    //####CodeMarker1Begin####       
    match e
        case Bool(_) => true
        case Int(_)  => true
        case Var(v)  => 
            if v in d then 
                // Does the declared type match the claimed type?
                d[v] == t 
            else 
                // This variable wasn't declared with a type!
                false  
        case BinaryOp(op, left, right) =>
            //var leftt:=ExprHasSecType(d,left,t);
            //var rightt:=ExprHasSecType(d,right,t);
            //if lhs&&rhs==true then true else false
           // match op
                //case Plus => leftt&&rightt
                //case Sub => leftt&&rightt
                //case Times => leftt&&rightt
                //case Leq => leftt&&rightt
                //case Eq => leftt&&rightt
            ExprHasSecType(d,left,t)&&ExprHasSecType(d,right,t)
            // TODO: Fill in this case
           //true
    //####CodeMarker1End####
}


// Define what it means for a command to be well typed.
// Notice that it recurses via CommandHasSecType (see below),
// which captures the CMD-RAISE rule discussed in lecture.
// When this predicate is true, that means that with 
// respect to the declarations (d), command c is well typed
predicate method CommandHasSecTypeBasic(d:SecDeclarations, c:Command, t:SecType) 
    decreases c, 0
{
    //####CodeMarker2Begin####
    match c
        case Noop => true

        case Assign(variable, e) => 
            if variable in d then 
                d[variable] == t && ExprHasSecType(d, e, t)
            else 
                false

        case Concat(c0, c1) =>
            CommandHasSecType(d, c0, t) && CommandHasSecType(d, c1, t)

        case IfThenElse(cond, ifTrue, ifFalse) =>
            ExprHasSecType(d, cond, t) && CommandHasSecType(d, ifTrue, t) &&
            CommandHasSecType(d, ifFalse, t)
            // TODO: Update this clause to perform the correct checks
           // true

        case While(cond, body) =>
            ExprHasSecType(d, cond, t) && CommandHasSecType(d, body, t)

        case PrintS(str) =>
            // TODO: Update this clause to perform the correct checks
            //true
            if t==Low then true else false

        case PrintE(e) =>
            ExprHasSecType(d, e, Low)  && t==Low
            // TODO: Update this clause to perform the correct checks
            //true

        case GetInt(variable) =>
            ExprHasSecType(d, Var(variable), Low)  && t==Low
            // TODO: Update this clause to perform the correct checks
            //true

        case GetSecretInt(variable) =>
            ExprHasSecType(d, Var(variable), High)  && t==High
            // TODO: Update this clause to perform the correct checks
            //true
    //####CodeMarker2End####
}

// A command can be well typed the basic way, 
// or via our command-lowering rule
predicate method CommandHasSecType(d:SecDeclarations, c:Command, t:SecType) 
    decreases c, 1
{
    CommandHasSecTypeBasic(d, c, t)

    // If the command is well typed at a higher security level (t'),
    // it's also okay to _use_ it a lower level (t)

    // This is the general form, but it creates automation challenges:
    // || (exists t' :: leq(t, t') && CommandHasSecTypeBasic(d, c, t'))    

    // For our lattice of {Low, High}, this is equivalent and easier to automate
    || (t.Low? && CommandHasSecTypeBasic(d, c, High))   
}


lemma NIexamples() {
    // Same command as before
    var x := Variable("x");
    var y := Variable("y");
    var cond := BinaryOp(Eq, Var(x), Int(1));
    var ifTrue := Assign(y, Int(1));
    var ifFalse := Assign(y, Int(0));
    var ite := IfThenElse(cond, ifTrue, ifFalse);   // ite says "if x = 1 { y := 1; } else { y := 0; }

    // Example: When both x and y are Low,
    //            then ite is well typed (at Low)
    var d := map[x := Low, y:= Low];
    assert ExprHasSecType(d, cond, Low);
    assert CommandHasSecType(d, ite, Low);

    // Example: When both x and y are High,
    //            then ite is well typed (at High)
    d := map[x := High, y:= High];
    assert ExprHasSecType(d, cond, High);
    assert CommandHasSecType(d, ite, High);

    // Example: When x is Low and y is High,
    //            then ite is well typed (at Low),
    //            thanks to our low-command typing rule
    d := map[x := Low, y:= High];
    assert ExprHasSecType(d, cond, Low);
    assert CommandHasSecType(d, ite, Low);

    // Example: PrintS should be Low only
    var printSCommand := PrintS("Hello");
    assert CommandHasSecType(d, printSCommand, Low);
    assert !CommandHasSecType(d, printSCommand, High);

    // Example: PrintE should work only on Low
    d := map[x := High, y:= Low];
    var printECommand2 := PrintE(Var(y));
    assert CommandHasSecType(d, printECommand2, Low);
    assert !CommandHasSecType(d, printECommand2, High);

    // Example: Y is a Low variable. Low should pass but High should fail
    var getIntCommand2 := GetInt(y);
    assert CommandHasSecType(d, getIntCommand2, Low);
    assert !CommandHasSecType(d, getIntCommand2, High);

    // Example: X is High variable. High should pass via the basic rules, 
    // but Low should pass too, thanks to the CMD-LWR rule 
    var getSecretIntCommand1 := GetSecretInt(x);
    assert CommandHasSecType(d, getSecretIntCommand1, High);
    assert CommandHasSecType(d, getSecretIntCommand1, Low);
}

//////////////////////////////////////////////////////////////////
//
//  Proof that our security type system ensures non-interference
//
//////////////////////////////////////////////////////////////////


/*** First define some helper functions to abbreviate long expressions ***/

// All variables declared in d as type t have the same value in s0 and s1
predicate VarsAgree(d:SecDeclarations, t:SecType, s0:Store, s1:Store) {
    forall variable :: 
        variable in d ==> 
            variable in s0 
            && variable in s1 
            && (d[variable] == t ==> s0[variable] == s1[variable])
}

// Decrement the fuel in s by 1
function DecrFuel(s:State) : State 
    requires s.fuel > 0
{
    s.(fuel := s.fuel - 1)
}

/*** Now define some helper lemmas ***/

// Helper Lemma 1
lemma NonInterfenceTypeExpr(d:SecDeclarations, s0:Store, s1:Store, e:Expr, t:SecType)
    // If we successfully evaluate an expression from two different stores (s0 and s1)
    requires EvalExpr(e, s0).ESuccess?
    requires EvalExpr(e, s1).ESuccess?
    // And the expression has type t
    requires ExprHasSecType(d, e, t)
    // And the two states agree on the value of all variables of type t
    requires VarsAgree(d, t, s0, s1)
    
    // Then the result of evaluating the expression is the same with both stores
    ensures  EvalExpr(e, s0) == EvalExpr(e, s1)
{
    //####CodeMarker3Begin####
    match e {
        case Bool(b) => 
        case Int(i)  => 
        case Var(v)  => 
        case BinaryOp(op, left, right) =>      
        // TODO: Update this case, so the proof goes through
    }
    //####CodeMarker3End####
}


// Helper Lemma 2
lemma HighCommandPreservesLowVars(d:SecDeclarations, c:Command, s:State, store':Store) 
    // If evaluating the command from state s produces store s'
    requires EvalCommand(s, c).Success? && EvalCommand(s, c).s == store'
    // and the command is well-typed at High
    requires CommandHasSecType(d, c, High)
    decreases s.fuel, c
    // Then s' has all the same variables that s.store did, 
    // and all low variables in store' have the same value they did in s.
    // In other words, the high command doesn't affect any of the low variables.
    ensures  forall v :: 
                v in s.store.Keys ==> 
                    v in store'.Keys 
                 && (v in d && d[v].Low? ==> store'[v] == s.store[v])
{
    //####CodeMarker4Begin####
    match c {
        case Noop =>  // Automatic
        case Assign(variable, e) => // Automatic       
        case Concat(c0, c1) =>
            var result := EvalCommand(s, c0);
            // Apply the induction hypothesis to the first command
            HighCommandPreservesLowVars(d, c0, s, result.s);
            // Apply the induction hypothesis to the second command
            HighCommandPreservesLowVars(d, c1, State(s.fuel, result.s, result.io), store');
        case IfThenElse(cond, ifTrue, ifFalse) => 
             var b := EvalExpr(cond, s.store).v.b;
                if b {
                    HighCommandPreservesLowVars(d, ifTrue, s, store');}
                else{
                    HighCommandPreservesLowVars(d, ifFalse, s, store');}
            // TODO: Update this case, so the proof goes through
        case While(cond, body) =>
            var b := EvalExpr(cond, s.store).v.b;
            if b {
                HighCommandPreservesLowVars(d, Concat(body, c), DecrFuel(s), store');
            }
        case PrintS(str) => // Automatic
        case PrintE(e) => // Automatic
        case GetInt(variable) => // Automatic
        case GetSecretInt(variable) => // Automatic
    }    
     //####CodeMarker4End####    
}


// Helper Lemma 3
lemma HighCommandPreservesPubIO(d:SecDeclarations, c:Command, s:State, r:CResult) 
    // If evaluating the command succeeds 
    requires EvalCommand(s, c) == r && r.Success?
    // and the command is well-typed at High
    requires CommandHasSecType(d, c, High)
    decreases s.fuel, c
    // Then no public values are read during the command's execution
    ensures  r.io.in_public == s.io.in_public
    // And nothing is written to the output
    ensures  r.io.output == s.io.output
{
    //####CodeMarker5Begin####
    match c {
        case Noop => // Automatic
        case Assign(variable, e) => // Automatic
        case Concat(c0, c1) =>
            var result := EvalCommand(s, c0);
            // Apply the induction hypothesis to the first command
            HighCommandPreservesPubIO(d, c0, s, result);
            // Apply the induction hypothesis to the second command
            HighCommandPreservesPubIO(d, c1, State(s.fuel, result.s, result.io), r);
        case IfThenElse(cond, ifTrue, ifFalse) => 
            // TODO: Update this case, so the proof goes through
            var b := EvalExpr(cond, s.store).v.b;
                if b {
                    HighCommandPreservesPubIO(d, ifTrue, s, r);}
                else{
                    HighCommandPreservesPubIO(d, ifFalse, s, r);}
        case While(cond, body) =>
            var b := EvalExpr(cond, s.store).v.b;
            if b {
                HighCommandPreservesPubIO(d, Concat(body, c), DecrFuel(s), r);
            }
        case PrintS(str) => // Automatic 
        case PrintE(e) => // Automatic 
        case GetInt(variable) => // Automatic
        case GetSecretInt(variable) => // Automatic
    }
    //####CodeMarker5End####      
}


// This is where most of the work of proving non-interference happens.
// It is an inductive argument over the structure of the program (c).
lemma NonInterferenceTypesInternal(d:SecDeclarations, c:Command, t:SecType, s0:State, s1:State, r0:CResult, r1:CResult) 
    // 0) The results passed in (r0 and r1) match the actual result of evaluating the command, starting from s0 and from s1 respectively
    requires EvalCommand(s0, c) == r0
    requires EvalCommand(s1, c) == r1

    // 1) Evaluation was successful
    requires r0.Success?
    requires r1.Success?

    // 1a) Initial IO states agree on the public inputs and the outputs
    requires s0.io.in_public == s1.io.in_public && s0.io.output == s1.io.output

    // 2) The command is well typed w.r.t. our security type system
    requires CommandHasSecType(d, c, t)
    
    // 3) The initial stores agree on the values of all Low variables
    requires VarsAgree(d, Low, s0.store, s1.store)

    decreases s0.fuel, s1.fuel, c // Helps Dafny see that our recursive argument does eventually terminate

    // Some additional invariants we'll need for our proof:
    //   a) After we execute the command, the value of the low variables stays the same in both stores
    ensures VarsAgree(d, Low, r0.s, r1.s)

    //   b) The public inputs we receive are the same in both executions
    ensures r0.io.in_public == r1.io.in_public
 
    // Conclusion: The output of both executions are identical
    //             (note that this holds even when the high variables differ!)
    ensures  r0.io.output == r1.io.output
{
    //####CodeMarker6Begin####
    match c {
        case Noop => // Automatic
        case Assign(variable, e) => 
        // TODO: Update this case, so the proof goes through
             if t.Low? {
                if CommandHasSecTypeBasic(d, c, t) {
                    NonInterfenceTypeExpr(d, s0.store, s1.store,e, t);
                } else {
                    assert CommandHasSecTypeBasic(d, c, High);
                    HighCommandPreservesLowVars(d, c, s0, r0.s);
                    HighCommandPreservesLowVars(d, c, s1, r1.s);   
                    HighCommandPreservesPubIO(d, c, s0, r0);
                    HighCommandPreservesPubIO(d, c, s1, r1); 
                }
            } else {
                HighCommandPreservesLowVars(d, c, s0, r0.s);
                HighCommandPreservesLowVars(d, c, s1, r1.s);
                HighCommandPreservesPubIO(d, c, s0, r0);
                HighCommandPreservesPubIO(d, c, s1, r1);
            }

        case Concat(c0, c1) =>
            var result0 := EvalCommand(s0, c0);
            var result1 := EvalCommand(s1, c0);
            if CommandHasSecTypeBasic(d, c, t) {
                var s0' := State(s0.fuel, result0.s, result0.io);
                var s1' := State(s1.fuel, result1.s, result1.io);
                NonInterferenceTypesInternal(d, c0, t, s0, s1, result0, result1);                 
                NonInterferenceTypesInternal(d, c1, t, s0', s1', r0, r1);
            } else {
                assert t.Low? && CommandHasSecTypeBasic(d, c, High);
                HighCommandPreservesLowVars(d, c, s0, r0.s);
                HighCommandPreservesLowVars(d, c, s1, r1.s);
                var s0' := State(s0.fuel, result0.s, result0.io);
                var s1' := State(s1.fuel, result1.s, result1.io);
                NonInterferenceTypesInternal(d, c0, High, s0, s1, result0, result1); 
                NonInterferenceTypesInternal(d, c1, High, s0', s1', r0, r1);
            }
        case IfThenElse(cond, ifTrue, ifFalse) =>
            if t.Low? {
                if CommandHasSecTypeBasic(d, c, t) {
                    NonInterfenceTypeExpr(d, s0.store, s1.store, cond, t);
                    if EvalExpr(cond, s0.store).v.b {
                        NonInterferenceTypesInternal(d, ifTrue, t, s0, s1, r0, r1);
                    } else {
                        NonInterferenceTypesInternal(d, ifFalse, t, s0, s1,r0, r1);
                    }
                } else {
                    assert CommandHasSecTypeBasic(d, c, High);
                    HighCommandPreservesLowVars(d, c, s0, r0.s);
                    HighCommandPreservesLowVars(d, c, s1, r1.s);   
                    HighCommandPreservesPubIO(d, c, s0, r0);
                    HighCommandPreservesPubIO(d, c, s1, r1); 
                }
            } else {
                HighCommandPreservesLowVars(d, c, s0, r0.s);
                HighCommandPreservesLowVars(d, c, s1, r1.s);
                HighCommandPreservesPubIO(d, c, s0, r0);
                HighCommandPreservesPubIO(d, c, s1, r1);
            }
        case While(cond, body) =>
            if t.Low? {
                if CommandHasSecTypeBasic(d, c, t) {
                    NonInterfenceTypeExpr(d, s0.store, s1.store, cond, t);                
                    if EvalExpr(cond, s0.store).v.b {
                        NonInterferenceTypesInternal(d, Concat(body, c), t, DecrFuel(s0), DecrFuel(s1), r0, r1);
                    }
                } else {
                    assert CommandHasSecTypeBasic(d, c, High);
                    HighCommandPreservesLowVars(d, c, s0, r0.s);
                    HighCommandPreservesLowVars(d, c, s1, r1.s);
                    HighCommandPreservesPubIO(d, c, s0, r0);
                    HighCommandPreservesPubIO(d, c, s1, r1);
                }
            } else {
                HighCommandPreservesLowVars(d, c, s0, r0.s);
                HighCommandPreservesLowVars(d, c, s1, r1.s);
                HighCommandPreservesPubIO(d, c, s0, r0);
                HighCommandPreservesPubIO(d, c, s1, r1);
            }
        case PrintS(str) => // Automatic 
        case PrintE(e) =>
            // TODO: Update this case, so the proof goes through
            if t.Low? {
                if CommandHasSecTypeBasic(d, c, t) {
                    NonInterfenceTypeExpr(d, s0.store, s1.store, e, t);
                } else {
                    assert CommandHasSecTypeBasic(d, c, High);
                    HighCommandPreservesLowVars(d, c, s0, r0.s);
                    HighCommandPreservesLowVars(d, c, s1, r1.s);   
                    HighCommandPreservesPubIO(d, c, s0, r0);
                    HighCommandPreservesPubIO(d, c, s1, r1); 
                }
            } else {
                HighCommandPreservesLowVars(d, c, s0, r0.s);
                HighCommandPreservesLowVars(d, c, s1, r1.s);
                HighCommandPreservesPubIO(d, c, s0, r0);
                HighCommandPreservesPubIO(d, c, s1, r1);
            }
        case GetInt(variable) => // Automatic
        case GetSecretInt(variable) => // Automatic 
    }
    //####CodeMarker6End####
}



// This is the top-level non-interference proof. 
// It says that our security type system really
// does enforce non-interference: No matter what
// the High variables are initially set to, and 
// no matter what Secret integers are read, the 
// public output is always the same.

// The signature for this lemma is all a human
// reviewer would need to read.  All of the proof
// above is mechanically checked.
lemma NonInterferenceTypes(d:SecDeclarations, c:Command, t:SecType, s0:State, s1:State, r0:CResult, r1:CResult) 
    // 0) The results passed in (r0 and r1) match the actual result of evaluating the command, starting from s0 and from s1 respectively
    requires EvalCommand(s0, c) == r0
    requires EvalCommand(s1, c) == r1

    // 1) Evaluation was successful
    requires r0.Success?
    requires r1.Success?

    // 2) The command is well typed w.r.t. our security type system
    requires CommandHasSecType(d, c, t)
    
    // 3) The initial stores agree on the values of all Low variables
    requires VarsAgree(d, Low, s0.store, s1.store)

    // 4) The initial IO states agree on the public inputs and the outputs
    requires s0.io.in_public == s1.io.in_public && s0.io.output == s1.io.output

    // Conclusion: The output of both executions are identical
    //             (note that this holds even when the high variables differ!)
    ensures  r0.io.output == r1.io.output
{
    NonInterferenceTypesInternal(d, c, t, s0, s1, r0, r1);
}
