# Answers for part 2.4 (Static vs. Dynamic Non-Interference)

TODO: Add your answers here!

2.4 Static vs. Dynamic Non-Interference (15 points)

* Q. (5 points) Without changing the code, is there any assignment of security labels to the variables (a, b, c, z)
that will allow this program to securely type check?
• If so, provide the necessary labels, state which label (i.e., Low or High) the program will type check
at, and explain how the relevant security typing rules will enable a successful type check. Hint: You
can test your labels by actually running the security type checker on the program! You still need to
explain why the type checking works, however.

Ans: 

* Q. • If the program cannot be type checked in our security type system, explain why not (1-2 paragraphs),
again, referring to the relevant typing rules.
(10 points) If you run this program through the current version of our taint checker, it will report a leak.
Improve the taint checker (hint: focus on EvalExprTaint) so that (a) this program and others like it run
successfully, without reporting a leak, and (b) all of the proofs of non-interference still hold.
Summarize, in 1-2 paragraphs, what you changed and why the proofs still hold.

Ans: Problem in old taint-checker: If any high value is multiplied with zero and the result is assigned to low variable, it used to report a leak. However, anything multiplied with zero will always return zero, hence, nothing is ever leaked. Therefore, the taint-checker should not be reporting any leak in that case.

Fix: In the EvalExprTaint, we changed the taint value of Times op, in case either of the LHS or RHS operands were equal to ZERO constant. In that case, we simply return the taint as false. And the taint checker no longer reports a leak in that case.

The proofs still hold because we're not really leaking any information about high variable by multiplying it with zero.

Previous code:
```c
case BinaryOp(op, lhs, rhs) => 
           var lhs:=EvalExprTaint(d,s,lhs,TInt);
           var rhs:=EvalExprTaint(d,s,rhs,TInt);        
           if (lhs.tainted==true  ||  rhs.tainted==true) then
               match op
                    case Plus  => TV(true,I(lhs.v.i +  rhs.v.i)) 
                    case Sub   => TV(true,I(lhs.v.i -  rhs.v.i)) 
                    case Times => TV(true,I(lhs.v.i *  rhs.v.i))
                    case Leq   => TV(true,B(lhs.v.i <= rhs.v.i))
                    case Eq    => TV(true,B(lhs.v.i == rhs.v.i))
           else
               match op                    
                    case Plus  => TV(false,I(lhs.v.i +  rhs.v.i)) 
                    case Sub   => TV(false,I(lhs.v.i -  rhs.v.i)) 
                    case Times => TV(false,I(lhs.v.i *  rhs.v.i)) 
                    case Leq   => TV(false,B(lhs.v.i <= rhs.v.i))
                    case Eq    => TV(false,B(lhs.v.i == rhs.v.i))
```

Updated code:
```c
case BinaryOp(op, lhs, rhs) => 
           var lhs:=EvalExprTaint(d,s,lhs,TInt);
           var rhs:=EvalExprTaint(d,s,rhs,TInt);        
           if (lhs.tainted==true  ||  rhs.tainted==true) then
               match op
                    case Plus  => TV(true,I(lhs.v.i +  rhs.v.i)) 
                    case Sub   => TV(true,I(lhs.v.i -  rhs.v.i)) 
                    case Times => if ((lhs.tainted==false && lhs.v==I(0)) || (rhs.tainted==false && rhs.v==I(0))) then TV(false, I(0)) else TV(true,I(lhs.v.i *  rhs.v.i))
                    case Leq   => TV(true,B(lhs.v.i <= rhs.v.i))
                    case Eq    => TV(true,B(lhs.v.i == rhs.v.i))
           else
               match op                    
                    case Plus  => TV(false,I(lhs.v.i +  rhs.v.i)) 
                    case Sub   => TV(false,I(lhs.v.i -  rhs.v.i)) 
                    case Times => TV(false,I(lhs.v.i *  rhs.v.i)) 
                    case Leq   => TV(false,B(lhs.v.i <= rhs.v.i))
                    case Eq    => TV(false,B(lhs.v.i == rhs.v.i))
```

# Extra Credit Writeup

TODO: 
If you decide to attempt the extra credit, for each section below, describe why
your program passes the security checks, how it leaks secret information, and
what limitation of the non-interference theorem your attack exploits.

## Security Type Leak

## Taint Analysis Leak
