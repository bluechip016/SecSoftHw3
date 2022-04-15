decl
  w:int; x:int;
begin
  w := get_secret_int();
  x := get_int();
  print_expr 3*x + 7*w; 
end
