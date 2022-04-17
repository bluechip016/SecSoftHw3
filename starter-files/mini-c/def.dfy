
//////////////////////////////////////////////////////////////////
//
//  Definition of our Abstract Syntax Trees (ASTs)
//
//////////////////////////////////////////////////////////////////

datatype Op = Plus | Sub | Times | Leq | Eq
datatype Variable = Variable(name:string)
datatype Expr = 
    | Bool(b:bool)
    | Int(i:int)
    | Var(v:Variable)
    | BinaryOp(op:Op, left:Expr, right:Expr)

datatype Command = 
    | Noop
    | Assign(v:Variable, e:Expr)
    | Concat(c0:Command, c1:Command)
    | IfThenElse(cond:Expr, ifTrue:Command, ifFalse:Command)
    | While(cond:Expr, body:Command)
    | PrintS(s:string)
    | PrintE(e:Expr)    
    | GetInt(v:Variable)
    | GetSecretInt(v:Variable)

//////////////////////////////////////////////////////////////////
//
//  Semantics of Expressions
//  (i.e., What does an expression _mean_?)
//
//////////////////////////////////////////////////////////////////

// Expressions evaluate to either a Boolean or an integer value
datatype Value = 
    | B(b:bool)
    | I(i:int)

// The Result type lets us indicate whether evaluating an
// expression fails or succeeds with a particular value
// (see EvalExpr for examples of when it might fail)
datatype EResult = EFail | ESuccess(v:Value)

// The store (or memory) maps variables to their values
type Store = map<Variable, Value>

// Semantics of expression evaluation
function method EvalExpr(e:Expr, store:Store) : EResult {
    match e        
        case Bool(b) => ESuccess(B(b))
        case Int(i)  => ESuccess(I(i))
        case Var(v)  => if v in store then ESuccess(store[v]) else EFail
        case BinaryOp(op, left, right) =>
            // First, evaluate the two expressions to (hopefully) get a value
            var left := EvalExpr(left, store);
            var right := EvalExpr(right, store);
            if left.EFail? || right.EFail? then 
                // If either evaluation failed, then we have to fail too
                EFail
            else if left.v.I? && right.v.I? then
                // If both operands are integers, perform the appropriate calculation
                match op                    
                    case Plus  => ESuccess(I(left.v.i +  right.v.i)) 
                    case Sub   => ESuccess(I(left.v.i -  right.v.i)) 
                    case Times => ESuccess(I(left.v.i *  right.v.i)) 
                    case Leq   => ESuccess(B(left.v.i <= right.v.i))
                    case Eq    => ESuccess(B(left.v.i == right.v.i))
            else
                EFail              
}

lemma ExprExamples() {
    var x := Variable("x");
    var e := BinaryOp(Plus, Int(5), Var(x));  // e is "5 + x"
    var s := map[x := I(2)];

    // Example
    assert EvalExpr(e, s).ESuccess?;  // Evaluation succeeds
    assert EvalExpr(e, s).v.i == 7;   // And we can statically prove what the result will be

    // Example
    e := BinaryOp(Leq, Var(x), Int(3));
    s := map[x := I(2)];
    assert EvalExpr(e, s).ESuccess?;   // Evaluation succeeds
    assert EvalExpr(e, s).v.b == true; // And we can statically prove what the result will be

    // Example
    // The same as Example 2, but we change the contents of the store,
    // so that the Boolean result is toggled the other way
    s := map[x := I(4)];
    assert EvalExpr(e, s).ESuccess?;   // Evaluation succeeds
    assert EvalExpr(e, s).v.b == false;// And we can statically prove what the result will be

    // Example
    // Here's an example where evaluation fails.  Note that we can still reason about such cases!
    s := map [];    // The store is empty, so variable lookups will fail
    assert EvalExpr(e, s).EFail?;

    // Example
    // Trying to multiply two mismatched types also fails
    e := BinaryOp(Times, Int(3), Bool(true));
    assert EvalExpr(e, s).EFail?;
}

//////////////////////////////////////////////////////////////////
//
//  Semantics of Commands
//
//////////////////////////////////////////////////////////////////


// Commands can interact with the outside world
// (e.g., by reading or writing data).  This type
// captures these actions by tracking all integers
// we read *from* the outside world, and all of the
// strings we write *to* the outside world.
// Note that these sequences are only used for proof purposes;
// i.e., we won't actually maintain either sequence 
// in our real executable code.  This is indicated below
// via the "ghost" keyword.  If you're curious, you can
// look at the C# code that Dafny generates and confirm
// that ghost Dafny variables never appear in C#.
datatype IO = IO(ghost in_public:seq<int>, 
                 ghost in_secret:seq<int>, 
                 ghost output:seq<string>)

// These trusted definitions let us actually interact
// with the outside world.  Notice the effect they have
// on the IO structure.  In Dafny, the "{:extern}" annotation
// says that the implementation will be provided separately
// (in our case, via some C# code).  An ensures clause on 
// an extern call is an assumption about the implementation;
// it's up to the developer of that implementation to make
// sure that assumption holds.
function method {:extern} PrintString(s:string, ghost io:IO) : (io':IO)
    // The IO that is returned is the same as before,
    // except the output is now longer by one entry
    ensures io' == io.(output := io.output + [s])

function method {:extern} ReadInt(ghost io:IO) : (int, IO)
    ensures 
        // The io that is returned is the same as before,
        // except the public input sequence is now longer by one entry,
        // which contains the integer that was returned
        var (i, io') := ReadInt(io);
        io' == io.(in_public := io.in_public + [i])

function method {:extern} ReadSecretInt(ghost io:IO) : (int, IO)
    ensures 
        // Same as for ReadInt
        var (i, io') := ReadSecretInt(io);
        io' == io.(in_secret := io.in_secret + [i])


// A few helper functions we'll need below
function method Bool2String(b:bool) : string {
    if b then "true" else "false"
}
function method {:extern} Int2String(i:int) : string

// A command may timeout, fail, or succeed and produce an updated 
// version of the store and the IO state
datatype CResult = Timeout | Fail | Success(s:Store, ghost io:IO)

// Here we define the meaning of each possible command.
// A command's behavior can depend on the current state
// of the store and the current state of the world (represented by IO),
// and if it succeeds, it can update one or both (as indicated by
// the members of the Success constructor)

// Note: Dafny requires all functions to terminate, but our Mini-C language allows
// the programmer to write infinite loops.  Hence, we introduce a
// somewhat artificial "fuel" parameter that ensures the Dafny function
// will always terminate (you can think of this as adding a timeout to
// the execution of the code).

// We summarize the "environment" in which the command executes
// in the State data structure:
datatype State = State(fuel:nat, store:Store, ghost io:IO)

function method EvalCommand(s:State, c:Command) : CResult 
    decreases s.fuel, c
{
    if s.fuel == 0 then Timeout  // We ran too long
    else
    match c
        case Noop => Success(s.store, s.io) // By definition, a no-op doesn't change anything

        case Assign(variable, e) =>     // variable := e
            // First evaluate the expression on the right-hand side
            var value := EvalExpr(e, s.store);
            (match value
                case EFail => Fail
                // If the expression on the right-hand side can be evaluated, 
                // we update the store to reflect the variable's new value
                case ESuccess(v) => Success(s.store[variable := v], s.io)
            )

        case Concat(c0, c1) =>           // c0 ; c1
            // First evaluate the left-hand side (c0)
            var result0 := EvalCommand(s, c0);
            (match result0
                // If c0 times out or fails, we do the same
                case Timeout => Timeout
                case Fail    => Fail
                case Success(store', io') => 
                    // If c0 succeeds, then we evaluate the right-hand side (c1)
                    EvalCommand(State(s.fuel, store', io'), c1)
            )

        case IfThenElse(cond, ifTrue, ifFalse) => // if cond then { ifTrue } else { ifFalse }
            // TODO: Update this clause to have the correct semantics
            var value:=EvalExpr(cond,s.store);
            (match value
                case EFail => Fail
                case ESuccess(I(_)) => Fail
                case ESuccess(B(b)) => 
                    if b then 
                        EvalCommand(State(s.fuel, s.store, s.io), ifTrue)
                    else
                        EvalCommand(State(s.fuel, s.store, s.io), ifFalse)

            )
            //Success(s.store, s.io)

        case While(cond, body) =>
            // First evaluate the conditional expression
            var value := EvalExpr(cond, s.store);
            (match value
                case EFail          => Fail  // If expression evaluation fails, so do we
                case ESuccess(I(_)) => Fail  // Unlike C, we do not allow integers to be used as Boolean conditions
                case ESuccess(B(b)) =>
                    if !b then 
                        // The while loop is complete
                        Success(s.store, s.io)                       
                    else
                        // Otherwise, execute the body, and then re-evaluate the while loop code (c)
                        EvalCommand(State(s.fuel - 1, s.store, s.io), Concat(body, c)))

        case PrintS(str) => 
            // TODO: Update this clause to have the correct semantics
            var io':=PrintString(str,s.io.(output:=[]));
            Success(s.store,io'.(output := s.io.output +[str]))
           // Success(s.store, s.io)

        case PrintE(e) =>
          // TODO: Update this clause to have the correct semantics
            var value:=EvalExpr(e,s.store);
            (
                match value
                case EFail => Fail
                case ESuccess(I(i)) =>
                     var str:= Int2String(i);
                     var io':=PrintString(str,s.io.(output:=[]));
                    Success(s.store,io'.(output := s.io.output +[str]))
                case ESuccess(B(b)) => 
                    var str:= Bool2String(b);
                    var io':=PrintString(str,s.io.(output:=[]));
                    Success(s.store,io'.(output := s.io.output +[str]))

            )
            //Success(s.store, io'.(output := s.io.output))
          
            //Success(s.store, s.io)

        case GetInt(variable) =>    // variable := GetInt()
            // Get an integer from the outside world, which gives us an updated IO record
            // Since this is a public input, we don't allow it to depend on the secrets
            // we've received so far, so we temporarily remove them from the IO
            var (i, io') := ReadInt(s.io.(in_secret := []));
            Success(s.store[variable := I(i)], io'.(in_secret := s.io.in_secret))

        case GetSecretInt(variable) =>    // variable := GetSecretInt()
            // TODO: Update this clause to have the correct semantics
            var (i, io') := ReadSecretInt(s.io.(in_secret := []));
            Success(s.store[variable := I(i)], io'.(in_secret := s.io.in_secret+[i]))
}


lemma CommandExamples(io:IO) {
    var x:Variable := Variable("x");    
    var store:Store := map[x := I(2)];
    var s:State := State(1, store, io);

    // Example: Noop has no effect
    assert EvalCommand(s, Noop).s == store;

    // Example: Assignment successfully mutates the store
    var c := Assign(x, Int(732));
    assert EvalCommand(s, c).Success?;
    assert EvalCommand(s, c).s == map[x := I(732)];

    // Example: Concatenation behaves sequentially
    c := Concat(Assign(x, Int(732)), Assign(x, Int(335)));
    assert EvalCommand(s, c).Success?;
    assert EvalCommand(s, c).s == map[x := I(335)];

    // Example: IfThenElse behaves as expected
    c := IfThenElse(Bool(true), Assign(x, Int(732)), Assign(x, Int(335)));
    assert EvalCommand(s, c).Success?;
    assert EvalCommand(s, c).s == map[x := I(732)];

    // Example: We can prove things about what gets printed
    c := Concat(PrintS("Hello"), PrintS("World"));
    assert EvalCommand(s, c).Success?;
    assert EvalCommand(s, c).io.output == io.output + ["Hello", "World"];
}


//////////////////////////////////////////////////////////////////
//
//  Typing Rules
//
//////////////////////////////////////////////////////////////////

// Mini-C only supports two types: integers and Booleans
datatype Type = TInt | TBool

// The program's declarations establish which type each variable has
type Declarations = map<Variable,Type>

// Define what it means for an expression to be well typed.
// When this predicate is true, that means that with 
// respect to the declarations (d), expression e has type t.
// Recall: "predicate" is just a function that returns bool
predicate method ExprHasType(d:Declarations, e:Expr, t:Type) {
    match e
        case Bool(_) => t.TBool?  // Boolean constants should be type TBool

        case Int(_)  => t.TInt?   // Integer constants should be type TInt

        case Var(v)  => 
            if v in d then
                // Does the declared type match the claimed type?
                d[v] == t 
            else 
                // This variable wasn't declared with a type!
                false 

        case BinaryOp(op, lhs, rhs) =>
            // TODO: Update this clause to perform the correct checks
            //true
            var lhs:=ExprHasType(d,lhs,t);
            var rhs:=ExprHasType(d,rhs,t);
            if lhs&&rhs==true then true else false
}

// Define what it means for a command to be well typed
// When this predicate is true, that means that with 
// respect to the declarations (d), command c is well typed
predicate method CommandWellTyped(d:Declarations, c:Command) {
    match c
        case Noop => true

        case Assign(variable, e) => 
            if variable in d then
                // Assignment is well typed if the expression's type
                // matches the declared type for the variable we are
                // assigning it to
                ExprHasType(d, e, d[variable])
            else
                // This variable wasn't declared with a type! 
                false

        case Concat(c0, c1) =>
            // Both commands must be well typed
            CommandWellTyped(d, c0) && CommandWellTyped(d, c1)

        case IfThenElse(cond, ifTrue, ifFalse) =>
            ExprHasType(d,cond,TBool) &&
            CommandWellTyped(d,ifTrue) &&
            CommandWellTyped(d,ifFalse)
            // TODO: Update this clause to perform the correct checks
            //true

        case While(cond, body) =>
            // We only allow Boolean conditionals, and the body must be well typed
            ExprHasType(d, cond, TBool) && CommandWellTyped(d, body)

        case PrintS(str) => 
            // TODO: Update this clause to perform the correct checks
            true
            //false

        case PrintE(e) => 
             //ExprHasType(d,e,)
            // TODO: Update this clause to perform the correct checks
            ExprHasType(d,e,TBool)||ExprHasType(d,e,TInt)

        case GetInt(variable) => 
            if variable in d then true else false
            // TODO: Update this clause to perform the correct checks

        case GetSecretInt(variable) =>
            // TODO: Update this clause to perform the correct checks
            if variable in d then true else false
}

lemma TypeExamples(io:IO) {
    var i:Variable := Variable("i");    
    var store:Store := map[i := I(2)];
    var d: Declarations := map[i := TInt];

    var b:Variable := Variable("b");    
    store := store[b := B(true)];
    d := d[b := TBool];

    var temp:Variable := Variable("temp");   

    var e1 := BinaryOp(Plus, Var(i), Int(3));

    var s:State := State(1, store, io);

    //Example: Check bool
    assert ExprHasType(d, Bool(true), TBool);

    //Example: Check var basic
    assert ExprHasType(d, Var(i), TInt);

    //Example: Check BinaryOp
    assert ExprHasType(d, e1, TInt);
}

// Finally, we define what it means for a store to be well typed.
// Essentially, we expect variables declared as Booleans to be
// storing Boolean values, and the same for integers.
predicate StoreWellTyped(d:Declarations, s:Store) {
    forall variable :: variable in d ==> 
        variable in s 
    && (d[variable].TBool? ==> s[variable].B?)
    && (d[variable].TInt? ==> s[variable].I?)
}
