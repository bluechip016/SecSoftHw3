decl
  w:int;
begin
  w := get_secret_int();
  while w <= 5 {
    print_string 'Looping';
    w := w + 1;
  }
end

