%{
  open OQAST
%}

%token <string> ID
%token <int> NInt
%token <float> Real
%token Pi
%token QReg CReg
%token Gate
%token CNOT H T Tdg
%token U X Y Z
%token Arrow
%token Measure Reset
%token LBracket RBracket
%token LBrace RBrace
%token LParen RParen
%token If
%token Plus Minus
%token Mult Div
%token Pow
%token DEquals
%token SemiColon Comma
%token EOF

%left Plus Minus        /* lowest precedence */
%left Mult Div Pow      /* medium precedence */
%nonassoc UMinus        /* highest precedence */

%start mainprogram
%type <OQAST.program> mainprogram

%%

mainprogram:
  | program EOF { $1 }

program:
  | statement         { [$1] }
  | statement program { $1 :: $2 }

statement:
  | decl                                  { Decl($1) }
  | gatedecl goplist RBrace               { GateDecl($1, $2) }
  | gatedecl RBrace                       { GateDecl($1, []) }
  | qop                                   { Qop($1) }
  | If LParen ID DEquals NInt RParen qop  { If($3, $5, $7) }

decl:
  | QReg ID LBracket NInt RBracket SemiColon { Qreg($2, $4) }
  | CReg ID LBracket NInt RBracket SemiColon { Creg($2, $4) }

gatedecl:
  | Gate ID idlist LBrace                       { ($2, None,    $3) }
  | Gate ID LParen RParen idlist LBrace         { ($2, None,    $5) }
  | Gate ID LParen idlist RParen idlist LBrace  { ($2, Some $4, $6) }

goplist:
 | uop                              { [Uop($1)] }
 | uop goplist                      { Uop($1) :: $2 }

qop:
  | uop                                       { Uop($1) }
  | Measure argument Arrow argument SemiColon { Meas($2, $4) }
  | Reset argument SemiColon                  { Reset($2) }

anylist:
  | idlist    { List.map (fun x -> (x, None)) $1 }
  | mixedlist { $1 }

explist:
  | exp               { [$1] }
  | exp Comma explist { $1 :: $3 }

idlist:
  | ID              { [$1] }
  | ID Comma idlist { $1 :: $3 }

mixedlist:
  | ID LBracket NInt RBracket                 { [($1, Some $3)] }
  | ID Comma mixedlist                        { ($1, None) :: $3 }
  | ID LBracket NInt RBracket Comma mixedlist { ($1, Some $3) :: $6 }
  | ID LBracket NInt RBracket Comma idlist    { ($1, Some $3) :: (List.map (fun x -> (x, None)) $6) }

uop:
  | CNOT argument Comma argument SemiColon      { CX($2, $4) }
  | H argument SemiColon                        { H($2) }
  | T argument SemiColon                        { T($2) }
  | Tdg argument SemiColon                      { Tdg($2) }
  | U LParen explist RParen argument SemiColon  { U($3, $5) }
  | X argument SemiColon                        { X($2) }
  | Y argument SemiColon                        { Y($2) }
  | Z argument SemiColon                        { Z($2) }
  | ID anylist SemiColon                        { Gate($1, [], $2) }
  | ID LParen RParen anylist SemiColon          { Gate($1, [], $4) }
  | ID LParen explist RParen anylist SemiColon  { Gate($1, $3, $5) }

argument:
  | ID                        { ($1, None) }
  | ID LBracket NInt RBracket { ($1, Some $3) }

exp:
  | Real                    { Real($1) }
  | NInt                    { Nninteger($1) }
  | Pi                      { Pi }
  | ID                      { Id($1) }
  | Minus exp %prec UMinus  { UMinus($2) }
  | exp binaryop exp        { Binaryop($1, $2, $3) }
  | LParen exp RParen       { $2 }

/* Source of a shift/reduce conflict */
binaryop:
  | Plus      { Plus }
  | Minus     { Minus }
  | Mult      { Mult }
  | Div       { Div }
  | Pow       { Pow }
