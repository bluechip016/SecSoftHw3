decl
  w:int;
begin
  w := get_secret_int();
  if w == 2 {
    print_string 'W is 2';
  } else {
    print_string 'W is not 2';
  }
end
