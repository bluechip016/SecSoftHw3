module Bridge {

	////////////////////////////////////////////////////////
	// DO NOT CHANGE THE FOLLOWING DEFINITIONS
	////////////////////////////////////////////////////////
	
	// Input Type: car at A, car at B, cars at both, cars at neither
	datatype Next_Car = A | B | Both | Neither

	datatype Traffic_Light = Red | Green

	datatype state = State(LightA: Traffic_Light, LightB: Traffic_Light, W_A:int, W_B:int, Cross_Counter:int)

	////////////////////////////////////////////////////////
	// DO NOT CHANGE THE DEFINITIONS ABOVE HERE
	////////////////////////////////////////////////////////

	predicate method Valid(s:state) {
		// WRITE a specification here based on the problem definition in the handout
		if(   (s.LightA==Green && s.LightB==Green) ||   ( s.W_A < 0  )   || (s.W_B < 0)  || ( s.Cross_Counter < 0)  )then false else true

	}

	////////////////////////////////////////////////////////
	// ADD additional pre- and post-conditions for each
	// method below, as needed, so everything verifies
	////////////////////////////////////////////////////////
	method Init() returns (s:state)
    ensures Valid(s)
	{
		s := State(Red, Red, 0, 0, 0);
	}

	method Increment_W_A(s:state) returns (s':state)
    requires Valid(s)
	requires(s.W_A>=0 && s.W_B>=0)
    ensures Valid(s')
	ensures (s'.W_A==s.W_A+1)
	ensures (s'.W_B==s.W_B)
	{
		s' := s.(W_A := s.W_A + 1);
	}

	method Increment_W_B(s:state) returns (s':state)
    requires Valid(s)
	requires(s.W_A>=0 && s.W_B>=0)
    ensures Valid(s')
	ensures (s'.W_A==s.W_A)
	ensures (s'.W_B==s.W_B+1)
	{
		s' := s.(W_B := s.W_B + 1);
	}

	method Increment_Cross_Counter(s:state) returns (s':state)
    requires Valid(s)
	requires(s.W_A>=0 && s.W_B>=0)
    ensures Valid(s')
	ensures(s'.W_A==s.W_A && s'.W_B==s.W_B && s'.Cross_Counter==s.Cross_Counter+1)
	{
		s' := s.(Cross_Counter := s.Cross_Counter + 1);
	}

	method Reset_Cross_Counter(s:state) returns (s':state)
    requires Valid(s)
	requires    (s.W_A>=0&&s.W_B>=0)  
    ensures Valid(s')
	ensures(s'.W_A==s.W_A && s'.W_B==s.W_B && s'.Cross_Counter==0)
	{
		s' := s.(Cross_Counter := 0);
	}
	
	method Cross(s:state) returns (s':state)
    requires Valid(s)
	requires  (  (  (s.W_A>0 ) &&(s.W_B>0) ) ||  (  (s.W_B==0)&&(s.LightA==Green)&&(s.W_A>0) ) || (    (s.W_A==0)&&(s.LightA!=Green)&&(s.W_B>0)      )  ) 
	//requires  (s.LightB==Green)&&(s.W_B > 0)     
    ensures Valid(s')
	ensures (s'.W_A>=0 &&s'.W_B>=0)
	{
		s' := s;
		if s.LightA.Green? {
			s' := s'.(W_A := s'.W_A - 1);
			s' := Increment_Cross_Counter(s');
		} else {
			s' := s'.(W_B := s'.W_B - 1);			
			s' := Increment_Cross_Counter(s');
		}
	}

	method Switch_Lights(s:state) returns (s':state)
    requires Valid(s)
	requires(s.W_A >= 0 && s.W_B >=0)
	requires (         (   (s.LightA==Red)&&(s.LightB==Green)    ) ||(          (s.LightA==Green)&&(s.LightB==Red)         )                   )
    ensures Valid(s')
	ensures  (         (   (s.LightA==Red)&&(s.LightB==Green)    ) ||(          (s.LightA==Green)&&(s.LightB==Red)         )                   )
	ensures( s'.W_A==s.W_A && s'.W_B==s.W_B)
	{
		s' := s;
		if s'.LightA.Red? {
			s' := s'.(LightA := Green);
		} else {
			s' := s'.(LightA := Red);
		}
		if s'.LightB.Red? {
			s' := s'.(LightB := Green);
		} else {
			s' := s'.(LightB := Red);
		}
	}
	
	method Tick(next:Next_Car, s:state) returns (s':state)
		requires Valid(s)
		//requires (s.LightA!=Green || s.LightB!=Green)
		//requires (  s.W_B>=0 && s.W_A>=0   )
		//requires (s.LightA!=Green)
		//requires (s.W_B>0) || (     (s.W_B==0) && (    (next==B) || (next==Both)    ||  ( s.Cross_Counter < 5 )       )              )
		//requires (    s.W_B>0     ) ||    (   (s.W_B==0 )   &&(   (next==B) ||   (s.W_A>0) ||   (next==Both) ||    (next==A)       ) )
		//requires (    s.W_A>0     ) ||    (   (s.W_A==0 )   &&(   (next==A) || (next==Both) || (s.W_B>0) || (next==B)  ) )
		ensures Valid(s')
	{
		s' := s;
		
		match next {
			case A => s' := Increment_W_A(s');
			case B => s' := Increment_W_B(s');
			case Both => s' := Increment_W_A(s'); s' := Increment_W_B(s');
			case Neither => s' := s';
		}
		
		

		if ((s'.W_A == 0) || (s'.W_B == 0)) && !(s'.W_A == 0 && s'.W_B == 0) {
			// Simple case
			s' := Reset_Cross_Counter(s');
			if s'.W_A > 0 {
				if s'.LightA.Red? {
					s' := s'.(LightA := Green, LightB := Red);
				}
				s' := s'.(W_A := s'.W_A - 1);
				s' := Increment_Cross_Counter(s');
			} else {
				if s'.LightB.Red? {
					s' := s'.(LightA := Red, LightB := Green);
				}
				s' := s'.(W_B := s'.W_B - 1);
				s' := Increment_Cross_Counter(s');				
			}
			// End of simple case
		} else if s'.W_A > 0 || s'.W_B > 0 {
			// Cars waiting on both sides
			if s'.LightA.Red? && s'.LightB.Red? {
				// Initial state, break the tie in favour of the A side
				s' := s'.(LightA := Green);
				s' := s'.(W_A := s'.W_A - 1);
				s' := Increment_Cross_Counter(s');				
			} else {
				if s'.Cross_Counter < 5 {
					s' := Cross(s');
				} else {
					s' := Switch_Lights(s');
					s' := Reset_Cross_Counter(s');
					s' := Cross(s');
				}
			}
		}
	}
}
