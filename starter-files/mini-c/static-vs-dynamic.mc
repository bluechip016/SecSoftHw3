decl
  a:int, Low; b:int, High; c:int, High; z:int, Low; 
begin
  a := get_int();
  b := get_secret_int();
  c := get_secret_int();

  if a <= 0 {
    b := b + 1;
    c := 0 * b;
    z := c;
  } else {
    b := 0 * c;
    c := c + 1;
    z := b;
  }

  print_expr z;
end
