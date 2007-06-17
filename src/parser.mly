%token IMP DEF COMMA DOT BSLASH LPAREN RPAREN TURN
%token IND INST APPLY CASE SEARCH TO ON WITH AND INTROS SKIP UNDO CUT
%token <int> NUM
%token <string> ID
%token EOF

%nonassoc BSLASH
%right IMP

%start term clauses command contexted_term
%type <Term.term> term
%type <Prover.clauses> clauses
%type <Prover.command> command
%type <Lppterm.obj> contexted_term

%%

contexted_term:
  | context TURN term                   { Lppterm.context_obj $1 $3 }
  | term                                { Lppterm.obj $1 }

context:
  | term COMMA context                  { Context.add $1 $3 }
  | term                                { Context.add $1 Context.empty }
      
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
  | term DOT                            { ($1, []) }
  | term DEF clause_body DOT            { ($1, $3) }

clause_body:
  | term COMMA clause_body              { $1::$3 }
  | term                                { [$1] }

command:
  | IND ON NUM DOT                      { Prover.Induction($3) }
  | APPLY ID TO id_arg_list DOT         { Prover.Apply($2, $4) }
  | CUT ID WITH ID                      { Prover.Cut($2, $4) }
  | INST ID WITH term DOT               { Prover.Inst($2, $4) }
  | CASE ID DOT                         { Prover.Case($2) }
  | SEARCH DOT                          { Prover.Search }
  | INTROS DOT                          { Prover.Intros }
  | SKIP DOT                            { Prover.Skip }
  | UNDO DOT                            { Prover.Undo }
  | EOF                                 { raise End_of_file }

id_arg_list:
  | ID AND id_arg_list                  { $1::$3 }
  | ID                                  { [$1] }
