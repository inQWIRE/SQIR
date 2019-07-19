%{
  open OQAST
%}

%token <OQAST.id> ID
%token <OQAST.nninteger> Idx
%token <OQAST.real> Real
%token Pi
%token QReg CReg
%token Gate
%token U CNOT
%token X Y Z H
%token Arrow
%token Measure Reset
/* %token Barrier */
%token LBracket RBracket
%token LBrace RBrace
%token LParen RParen
/* %token Equal */
%token Mult Div
%token Plus Minus
%token SemiColon Comma
%token EOF

%start mainprogram
%type <OQAST.program> mainprogram

%%

mainprogram:
  | program EOF { $1 }

program:
  | statement         { [$1] }
  | statement program { $1 :: $2 }

statement:
  | decl                    { Decl($1) }
  | gatedecl goplist RBrace { Newgate($1, $2) }
  | gatedecl RBrace         { Newgate($1, []) }
  /* | Opaque id idlist SemiColon { $1 $2 $3 }
  | Opaque id LParen RParen idlist SemiColon { $1 $2 $5 }
  | Opaque id LParen idlist RParen idlist SemiColon { $1 $2 $4 $6 } */
  | qop                     { Qop($1) }
  /* | "if (" id "==" Idx ")" qop */
  /* | Barrier anylist { Barrier($2) } */

decl:
  | QReg ID LBracket Idx RBracket SemiColon { Qreg($2, $4) }
  | CReg ID LBracket Idx RBracket SemiColon { Creg($2, $4) }

gatedecl:
  | Gate ID idlist LBrace                       { ($2, None, $3) }
  | Gate ID LParen RParen idlist LBrace         { ($2, None, $5) }
  | Gate ID LParen idlist RParen idlist LBrace  { ($2, Some $4, $6) }

goplist:
 | uop                              { [Uop($1)] }
 /* | Barrier idlist SemiColon         { [Barrier($2)] } */
 | uop goplist                      { Uop($1) :: $2 }
 /* | Barrier idlist SemiColon goplist { Barrier($2) :: $4 } */

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
  | ID LBracket Idx RBracket                  { [($1, Some $3)] }
  | ID Comma mixedlist                        { ($1, None) :: $3 }
  | ID LBracket Idx RBracket Comma mixedlist  { ($1, Some $3) :: $6 }
  | ID LBracket Idx RBracket Comma idlist     { ($1, Some $3) :: (List.map (fun x -> (x, None)) $6) }

uop:
  | U LParen explist RParen argument SemiColon  { U($3, $5) }
  | CNOT argument Comma argument SemiColon      { CX($2, $4) }
  | X argument SemiColon                        { X($2) }
  | Y argument SemiColon                        { Y($2) }
  | Z argument SemiColon                        { Z($2) }
  | H argument SemiColon                        { H($2) }
  | ID anylist SemiColon                        { Gate($1, [], $2) }
  | ID LParen RParen anylist SemiColon          { Gate($1, [], $4) }
  | ID LParen explist RParen anylist SemiColon  { Gate($1, $3, $5) }

argument:
  | ID                        { ($1, None) }
  | ID LBracket Idx RBracket  { ($1, Some $3) }

exp:
  | Real              { Real($1) }
  | Idx               { Nninteger($1) }
  | Pi                { Pi }
  | ID                { Id($1) }
  | exp binaryop exp  { Binaryop($1, $2, $3) }
  /* | Minus exp         { Neg($2) } */
  | LParen exp RParen { $2 }
  /* | unaryop LParen exp RParen */

binaryop:
  | Plus      { Plus }
  | Minus     { Minus }
  | Mult      { Mult }
  | Div       { Div }
  /* | Pow       { Pow } */
