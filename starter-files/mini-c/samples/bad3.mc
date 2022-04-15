decl
  w:int; x:int;
begin
  w := get_secret_int();
  x := get_int();
  print_expr x; 
  print_expr w;
end
