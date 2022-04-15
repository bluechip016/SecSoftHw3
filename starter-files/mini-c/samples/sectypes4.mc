
decl
  x:int,High;
  y:int,Low;
begin
  x := get_secret_int();
  y := get_int();
  if y == 0 {
    print_string 'It is 0';
  } else {
    print_string 'It is not 0';
  }
end
