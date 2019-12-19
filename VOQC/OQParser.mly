%{
  open OQAST
%}

%token <string> ID
%token <int> NINT
%token <float> REAL
%token <string> STRING

%token OPENQASM INCLUDE
%token SEMICOLON ";" COMMA ","
%token EQUALS "==" ARROW "->"
%token LBRACE "{" RBRACE "}"
%token LPAREN "(" RPAREN ")"
%token LBRACKET "[" RBRACKET "]"
%token OPAQUE BARRIER
%token IF
%token QREG CREG
%token GATE
%token MEASURE RESET
%token U CX
%token PI
%token PLUS "+" MINUS "-"
%token TIMES "*" DIV "/"
%token POW "^"
%token SIN COS TAN EXP LN SQRT
%token EOF

%left PLUS MINUS
%left TIMES DIV
%left UMINUS
%right POW

%start <OQAST.program> mainprogram

%%

mainprogram: OPENQASM REAL ";" p = program EOF { p }

program: sl = statement* { sl }

statement:
  | INCLUDE inc = STRING ";"                                    { Include(inc) }
  | d = decl                                                    { Decl(d) }
  | gd = gatedecl "{" gl = goplist "}"                          { GateDecl(gd, gl) }
  | OPAQUE name = ID qargs = idlist ";"                         { OpaqueDecl(name, [], qargs) }
  | OPAQUE name = ID "(" params = idlist ")" qargs = idlist ";" { OpaqueDecl(name, params, qargs) }
  | q = qop                                                     { Qop(q) }
  | IF "(" creg = ID "==" n = NINT ")" q = qop                  { If(creg, n, q) }
  | BARRIER qargs = anylist ";"                                 { Barrier(qargs) }

decl:
  | QREG name = ID "[" size = NINT "]" ";" { QReg(name, size) }
  | CREG name = ID "[" size = NINT "]" ";" { CReg(name, size) }

gatedecl:
  | GATE name = ID qargs = idlist                         { (name, [], qargs) }
  | GATE name = ID "(" params = idlist ")" qargs = idlist { (name, params, qargs) }

goplist: body = uop_or_barrier* { body }

uop_or_barrier:
 | u = uop                    { GUop(u) }
 | BARRIER qargs = idlist ";" { GBarrier(qargs) }

qop:
  | u = uop                                           { Uop(u) }
  | MEASURE qarg = argument "->" carg = argument ";"  { Meas(qarg, carg) }
  | RESET qarg = argument ";"                         { Reset(qarg) }

uop:
  | CX q1 = argument "," q2 = argument ";"                  { CX(q1, q2) }
  | U "(" params = explist ")" q = argument ";"             { U(params, q) }
  | gname = ID qargs = anylist ";"                          { Gate(gname, [], qargs) }
  | gname = ID "(" params = explist ")" qargs = anylist ";" { Gate(gname, params, qargs) }

anylist: al = separated_list(",", argument) { al }

idlist: il = separated_list(",", ID) { il }

argument:
  | name = ID                     { (name, None) }
  | name = ID "[" idx = NINT "]"  { (name, Some idx) }

explist: el = separated_list(",", exp) { el }

exp:
  | r = REAL                      { Real(r) }
  | n = NINT                      { Nninteger(n) }
  | PI                            { Pi }
  | id = ID                       { Id(id) }
  | e1 = exp "+" e2 = exp         { BinaryOp(Plus, e1, e2) }
  | e1 = exp "-" e2 = exp         { BinaryOp(Minus, e1, e2) }
  | e1 = exp "*" e2 = exp         { BinaryOp(Times, e1, e2) }
  | e1 = exp "/" e2 = exp         { BinaryOp(Div, e1, e2) }
  | "-" e = exp %prec UMINUS      { UnaryOp(UMinus, e) }
  | e1 = exp "^" e2 = exp         { BinaryOp(Pow, e1, e2) }
  | "(" e = exp ")"               { e }
  | uo = unaryop "(" e = exp ")"  { UnaryOp(uo, e) }

unaryop:
  | SIN   { Sin }
  | COS   { Cos }
  | TAN   { Tan }
  | EXP   { Exp }
  | LN    { Ln }
  | SQRT  { Sqrt }
