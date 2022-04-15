
decl
  a:int, ; b:int, ; c:int, ; d:int, ;
  x:int, ; y:int, ; z:int, ;
begin
  a := get_secret_int();
  b := get_secret_int();
  c := get_int();
  d := get_int();

  x := a + b;
  y := c + d;

  if 10 <= y {
    x := x + x;

    if c <= d {
      a := x + a;
    } else {
      a := x + b;
    }
  } else {
    if d <= c {
      b := x + b;
    } else {
      b := x + a;
    }
  }
  
  if 10 <= y {
    z := c - 2;
  } else {
    z := c + 2;
  }

  print_expr c;
  print_expr d;
end
