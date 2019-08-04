%{
  open OQAST
%}

%token <string> ID
%token <int> NINT
%token <float> REAL

%token OPENQASM
%token SEMICOLON COMMA
%token EQUALS ARROW
%token LBRACE RBRACE
%token LPAREN RPAREN
%token LBRACKET RBRACKET
/* %token OPAQUE BARRIER */
%token IF
%token QREG CREG
%token GATE
%token MEASURE RESET
%token U CX
%token PI
%token PLUS MINUS
%token TIMES DIV
%token POW
/* %token SIN COS TAN EXP LN SQRT */
%token EOF

%left PLUS MINUS
%left TIMES DIV
%right POW
%left UMINUS

%start <OQAST.program> mainprogram

%%

mainprogram:
  | OPENQASM REAL SEMICOLON program EOF { $4 }

program:
  | statement         { [$1] }
  | statement program { $1 :: $2 }

statement:
  | decl                                  { Decl($1) }
  | gatedecl goplist RBRACE               { GateDecl($1, $2) }
  | gatedecl RBRACE                       { GateDecl($1, []) }
  | qop                                   { Qop($1) }
  | IF LPAREN ID EQUALS NINT RPAREN qop   { If($3, $5, $7) }

decl:
  | QREG ID LBRACKET NINT RBRACKET SEMICOLON { Qreg($2, $4) }
  | CREG ID LBRACKET NINT RBRACKET SEMICOLON { Creg($2, $4) }

gatedecl:
  | GATE ID idlist LBRACE                       { ($2, None,    $3) }
  | GATE ID LPAREN RPAREN idlist LBRACE         { ($2, None,    $5) }
  | GATE ID LPAREN idlist RPAREN idlist LBRACE  { ($2, Some $4, $6) }

goplist:
 | uop                              { [Uop($1)] }
 | uop goplist                      { Uop($1) :: $2 }

qop:
  | uop                                       { Uop($1) }
  | MEASURE argument ARROW argument SEMICOLON { Meas($2, $4) }
  | RESET argument SEMICOLON                  { Reset($2) }

anylist:
  | idlist    { List.map (fun x -> (x, None)) $1 }
  | mixedlist { $1 }

explist:
  | exp               { [$1] }
  | exp COMMA explist { $1 :: $3 }

idlist:
  | ID              { [$1] }
  | ID COMMA idlist { $1 :: $3 }

mixedlist:
  | ID LBRACKET NINT RBRACKET                 { [($1, Some $3)] }
  | ID COMMA mixedlist                        { ($1, None) :: $3 }
  | ID LBRACKET NINT RBRACKET COMMA mixedlist { ($1, Some $3) :: $6 }
  | ID LBRACKET NINT RBRACKET COMMA idlist    { ($1, Some $3) :: (List.map (fun x -> (x, None)) $6) }

uop:
  | CX argument COMMA argument SEMICOLON        { CX($2, $4) }
  | U LPAREN explist RPAREN argument SEMICOLON  { U($3, $5) }
  | ID anylist SEMICOLON                        { Gate($1, [], $2) }
  | ID LPAREN RPAREN anylist SEMICOLON          { Gate($1, [], $4) }
  | ID LPAREN explist RPAREN anylist SEMICOLON  { Gate($1, $3, $5) }

argument:
  | ID                        { ($1, None) }
  | ID LBRACKET NINT RBRACKET { ($1, Some $3) }

exp:
  | REAL                    { Real($1) }
  | NINT                    { Nninteger($1) }
  | PI                      { Pi }
  | ID                      { Id($1) }
  | exp PLUS exp            { Binaryop($1, Plus, $3) }
  | exp MINUS exp           { Binaryop($1, Minus, $3) }
  | exp TIMES exp           { Binaryop($1, Times, $3) }
  | exp DIV exp             { Binaryop($1, Div, $3) }
  | exp POW exp             { Binaryop($1, Pow, $3) }
  | MINUS exp %prec UMINUS  { UMinus($2) }
  | LPAREN exp RPAREN       { $2 }
