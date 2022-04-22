
decl
  b:int, High ;
begin
  b := get_secret_int();
  if b <= 0 {
      if b == 0 {
        b := 0;
      } else {
        b := 1;
        while b <= 100 {
            b := b+1;
        }
      }
  } else {
      b := 1;
      while b <= 1000 {
            b := b+1;
        }
    }
end