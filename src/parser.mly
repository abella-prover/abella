%token BSLASH LPAREN RPAREN
%token FORALL IMP RARROW COLON COMMA
%token LBRACKET RBRACKET
%token STAR AT
%token IND APPLY CASE SEARCH TO ON AND THEOREM INTROS
%token <int> NUM
%token DEF DOT
%token <string> ID
%token EOF

%nonassoc BSLASH
%right IMP

%start lppterm term clauses command
%type <Lppterm.lppterm> lppterm
%type <Term.term> term
%type <Prover.clauses> clauses
%type <Prover.command> command

%%

lppterm:
  | FORALL binding_list COMMA lppterm { Lppterm.forall $2 $4 }
  | object_term RARROW lppterm        { Lppterm.arrow $1 $3 }
  | object_term                       { $1 }

binding_list:
  | binding binding_list              { $1::$2 }
  | binding                           { [$1] }

binding:
  | ID                                { $1 }

object_term:
  | LBRACKET term RBRACKET            { Lppterm.obj $2 }
  | LBRACKET term RBRACKET stars      { Lppterm.active_obj $2 $4 }
  | LBRACKET term RBRACKET ats        { Lppterm.inactive_obj $2 $4 }

stars:
  | stars STAR                        { $1 + 1 }
  | STAR                              { 1 }

ats:
  | ats AT                            { $1 + 1 }
  | AT                                { 1 }
      
term:
  | term IMP term                     { Term.app (Term.atom "=>") [$1; $3] }
  | ID BSLASH term                    { Term.abstract $1 $3 }
  | exp exp_list                      { Term.app $1 $2 }
  | exp                               { $1 }
      
exp:
  | LPAREN term RPAREN                { $2 }
  | ID                                { Term.const $1 0 }
      
exp_list:
  | exp exp_list                      { $1::$2 }
  | exp                               { [$1] }
  | ID BSLASH term                    { [Term.abstract $1 $3] }

clauses:
  | clause clauses                    { $1::$2 }
  |                                   { [] }

clause:
  | term DOT                          { (Lppterm.obj $1, []) }
  | term DEF clause_body DOT          { (Lppterm.obj $1, $3) }

clause_body:
  | term COMMA clause_body            { (Lppterm.obj $1)::$3 }
  | term                              { [Lppterm.obj $1] }

command:
  | IND ON num_arg_list DOT           { Prover.Induction($3) }
  | APPLY ID TO id_arg_list DOT       { Prover.Apply($2, $4) }
  | CASE ID DOT                       { Prover.Case($2) }
  | SEARCH DOT                        { Prover.Search }
  | THEOREM lppterm DOT               { Prover.Theorem($2) }
  | INTROS DOT                        { Prover.Intros }

num_arg_list:
  | NUM AND num_arg_list              { $1::$3 }
  | NUM                               { [$1] }

id_arg_list:
  | ID AND id_arg_list                { $1::$3 }
  | ID                                { [$1] }
   

