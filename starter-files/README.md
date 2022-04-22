# Answers for part 2.4 (Static vs. Dynamic Non-Interference)

TODO: Add your answers here!

2.4 Static vs. Dynamic Non-Interference (15 points)
## Part 1:
`Q:`(5 points) Without changing the code, is there any assignment of security labels to the variables (a, b, c, z)
that will allow this program to securely type check?

`Ans`: The program cannot be type checked in our security type system. 
Explanation: 
From part of :
```c
a := get_int();
b := get_secret_int();
c := get_secret_int();
```
We can know that `SecType` of a,b,c is `Low`,`High`, and `High`. 
So, if `SecType` of z is `Low`, according to the code: 
```c
case Assign(variable, e) => 
            if variable in d then 
                d[variable] == t && ExprHasSecType(d, e, t)
            else 
                false
```
the part of `z := c;` and `z := b;` will cause `flase`, becase b and c have `SecType` of `High`.
However, if `SecType` of z is `High`, according to the code: 
```c
case PrintE(e) =>
            ExprHasSecType(d, e, Low)  && t==Low
```
the part of ` print_expr z;` will also cause `flase`, becase b and c have `SecType` of `High`.

## Part 2
` Q:`  (10 points) If you run this program through the current version of our taint checker, it will report a leak.
Improve the taint checker (hint: focus on EvalExprTaint) so that (a) this program and others like it run
successfully, without reporting a leak, and (b) all of the proofs of non-interference still hold.
Summarize, in 1-2 paragraphs, what you changed and why the proofs still hold.

`Ans:` Problem in old taint-checker: If any high value is multiplied with zero and the result is assigned to low variable, it used to report a leak. However, anything multiplied with zero will always return zero, hence, nothing is ever leaked. Therefore, the taint-checker should not be reporting any leak in that case.

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

Code used for exploitation:

type-leak.mc:
```c

decl
  b:int, High ; c:int, High;
begin
  b := get_secret_int();
  c := 1;
  if b <= 0 {
      if b == 0 {
        b := 0;
      } else {
        b := 1;
        while b <= 26 {
            b := b+1;
            c := c*c;
            c := c+b;
        }
        c := c+b;
      }
  } else {
        b := 5;
        while b <= 15 {
            b := b+1;
            c := b*c;
            c := c*c;
            c := c*c+b;
        }
        c := c-b;
    }
end
```
tyle_leak_attack.py:

```c
def attack(output, elapsed):
    if elapsed > 20:
        return "Less than zer0"
    elif elapsed > 5:
        return "Greater than zer0"
    else:
        return "Equal to zer0"
```

` Q:` Why our program passes the security check?
` Ans:` Our program passes the security checks because we have preserved the non-interference theorem in the attack. Only `High` variables have been used and the conditionals also have `High` conditional affecting `High` variables effect. Also, we haven't used any print expression or string in our code anywhere, especially not in the `High` conditionals. Therefore, non-intereference is well-preserved.

` Q:` How it leaks secret information?
` Ans:` Our program uses the side channel attack to leak the information. The code takes 3 branches: on secrect being -ve, +ve or ZERO. All 3 branches have different sets of statements, crafted in a way, such that the branches have different execution times.

` Q:`  What limitation of the non-interference theorem your attack exploits?
` Ans:` Non-interference theorem does not protect the application from timing attacks. i.e. it does not prevent conditional branches from having heavy executions. The computations should be enforced outside the conditional branches, so that the attacker cannot cannot differentiate the secrets based on execution times of each branch.


## Taint Analysis Leak
