module Prime {
	////////////////////////////////////////////////////////
	// DO NOT CHANGE THE SPECIFICATION
	////////////////////////////////////////////////////////
	predicate method prime(n:int)
	{
		n >= 2 && forall i :: 2 <= i < n ==> n % i != 0
	}

	method IsPrime(n:nat) returns (res:bool)
		requires n >= 2
		ensures res <==> prime(n)
	{
		// WRITE an implementation here that will satisfy the postcondition
		res:=true;
		var i:=2;
		while(i<n)
			invariant forall j :: 2 <= j < i ==> n%j!=0
			invariant 2<= i<=n
			{
				if(n%i==0){
					return false;
				}
				i:=i+1;
			}
			
	}
}
