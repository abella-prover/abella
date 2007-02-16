%token IMP DEF COMMA DOT BSLASH LPAREN RPAREN
%token IND INST APPLY CASE SEARCH TO ON WITH AND INTROS
%token <int> NUM
%token <string> ID
%token EOF

%nonassoc BSLASH
%right IMP

%start term clauses command
%type <Term.term> term
%type <Prover.clauses> clauses
%type <Prover.command> command

%%

term:
  | term IMP term                       { Term.binop "=>" $1 $3 }
  | ID BSLASH term                      { Term.abstract $1 $3 }
  | exp exp_list                        { Term.app $1 $2 }
  | exp                                 { $1 }
      
exp:
  | LPAREN term RPAREN                  { $2 }
  | ID                                  { Term.const $1 }
      
exp_list:
  | exp exp_list                        { $1::$2 }
  | exp                                 { [$1] }
  | ID BSLASH term                      { [Term.abstract $1 $3] }

clauses:
  | clause clauses                      { $1::$2 }
  |                                     { [] }

clause:
  | term DOT                            { (Lppterm.obj $1, []) }
  | term DEF clause_body DOT            { (Lppterm.obj $1, $3) }

clause_body:
  | term COMMA clause_body              { (Lppterm.obj $1)::$3 }
  | term                                { [Lppterm.obj $1] }

command:
  | IND ON num_arg_list DOT             { Prover.Induction($3) }
  | APPLY ID TO id_arg_list DOT         { Prover.Apply($2, $4) }
  | INST ID WITH term DOT               { Prover.Inst($2, $4) }
  | CASE ID DOT                         { Prover.Case($2) }
  | SEARCH DOT                          { Prover.Search }
  | INTROS DOT                          { Prover.Intros }
  | EOF                                 { raise End_of_file }

num_arg_list:
  | NUM AND num_arg_list                { $1::$3 }
  | NUM                                 { [$1] }

id_arg_list:
  | ID AND id_arg_list                  { $1::$3 }
  | ID                                  { [$1] }
   

