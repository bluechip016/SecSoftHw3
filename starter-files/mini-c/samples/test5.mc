decl
  x:int;
  y:int;
begin
  x := get_int();
  y := 0;

  while x <= 5 {
    print_string 'Loop: ';
    print_expr y;
    x := x + 1;
    y := y + 1;
  }
end



