decl
  w:int; x:int;
begin
  w := get_secret_int();
  x := get_int();
  if x == w {
    print_string 'Equal';
  } else {
    print_string 'Not Equal';
  }
end
