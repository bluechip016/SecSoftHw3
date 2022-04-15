grammar MiniC;

/*
 * Parser Rules
 */

program
	: 'decl' declarations 'begin' block 'end' EOF
	;

declarations
  : decl*
  ;

decl
  : v=id ':' t=type (',' s=sectype)? ';'
  ;

type
  : 'bool'
  | 'int'
  ;

sectype
  : 'Low'
  | 'High'
  ;

block
	: lc=command b=block 
	| c=command
	;

command
	: noopCommand ';'
	| assignCommand ';'
	| ifCommand
	| whileCommand
	| printSCommand ';'
	| printECommand ';'
	| getIntCommand ';'
	| getSecretIntCommand ';'
	;

noopCommand
	: 'noop'
	;

assignCommand
	: v=id ':=' e=exp
	;

ifCommand
	: 'if' cond=exp '{' ifTrue=block '} else {' ifFalse=block '}'
	;

whileCommand
	: 'while' cond=exp '{' body=block '}'
	;

printSCommand
  : 'print_string' s=Single_string
  ;

printECommand
  : 'print_expr' e=exp
  ;

getIntCommand
  : v=id ':= get_int()'
  ;

getSecretIntCommand
  : v=id ':= get_secret_int()'
  ;

exp
	: b=bool
  | i=integer
  | v=id
  | left=exp op='+'  right=exp
  | left=exp op='-'  right=exp
  | left=exp op='*'  right=exp
  | left=exp op='<=' right=exp
  | left=exp op='==' right=exp
	;

id
	: name=Identifier
	;

integer
	: val=Int
	;

bool
	: val=(True|False)
	;

True : 'true';
False : 'false';

/*
 * Lexer Rules
 */

Identifier
	: Nondigit (Nondigit | Digit)*
	;

Int
	: ('-')? Digit+
	;

fragment Nondigit
	: [a-zA-Z]
	;

fragment Digit
	: [0-9]
	;

Single_string
    : '\'' ~('\'')+ '\''
    ;

WS
	: (' '|'\t'|'\n'|'\r'|'\r\n')+ -> skip
	;

