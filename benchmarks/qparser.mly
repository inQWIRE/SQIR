%{
  open Ast
%}

%token QG
%token LB RB LP RP
%token WC WN
%token EQ PLS CLN CMA
%token H Z X
%token QB CB
%token IN
%token OUT
%token <int> ID
%token EOF


%start program
%type <Ast.program> program


%%

program :
  | inputs qgates outputs EOF { $2 }

;

bit:
  | QB { () }
  | CB { () }


;

register_decl:
  | ID CLN bit { ($1, $3) }

;

register_decls:
  | register_decl { [ $1 ] }
  | register_decl CMA register_decls { $1 :: $3 }

;

outputs:
  | OUT CLN register_decls { $3 }

;

inputs:
  | IN CLN register_decls { $3 }

;

value:
  | PLS ID { $2 }

;

values:
  | value { [ $1 ] }
  | value CMA values { $1 :: $3 }

;

control:
  | WC EQ LB values RB { $4 }

;

controls:
  | { [] }
  | control controls { $1 :: $2 }

;

typ:
  | X { X }
  | H { H }
  | Z { Z }

;

qgate:
  | QG LB typ RB LP ID RP controls WN { ($3, $6, $8) }

;

qgates:
  | qgate { [ $1 ] }
  | qgate qgates { $1 :: $2 }
