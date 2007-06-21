%token IMP DEF COMMA DOT BSLASH LPAREN RPAREN TURN
%token IND INST APPLY CASE SEARCH TO ON WITH AND INTROS SKIP UNDO CUT
%token COLON RARROW FORALL EXISTS STAR AT THEOREM OR LBRACK RBRACK

%token <int> NUM
%token <string> ID
%token EOF

/* Lower */
  
%nonassoc COMMA
%right RARROW
%left OR
  
%nonassoc BSLASH
%right IMP

/* Higher */


%start lppterm term clauses top_command command contexted_term
%type <Term.term> term
%type <Prover.clauses> clauses
%type <Prover.command> command
%type <Lppterm.obj> contexted_term
%type <Lppterm.lppterm> lppterm
%type <Prover.top_command> top_command

%%

contexted_term:
  | context TURN term                   { Lppterm.context_obj $1 $3 }
  | term                                { Lppterm.obj $1 }

context:
  | context COMMA term                  { Context.add $3 $1 }
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

lppterm:
  | FORALL binding_list COMMA lppterm   { Lppterm.Forall($2, $4) }
  | EXISTS binding_list COMMA lppterm   { Lppterm.Exists($2, $4) }
  | lppterm RARROW lppterm              { Lppterm.Arrow($1, $3) }
  | lppterm OR lppterm                  { Lppterm.Or($1, $3) }
  | LPAREN lppterm RPAREN               { $2 }
  | object_term                         { $1 }
  | term                                { Lppterm.Pred($1) }

binding_list:
  | binding binding_list                { $1::$2 }
  | binding                             { [$1] }

binding:
  | ID                                  { $1 }

object_term:
  | LBRACK contexted_term RBRACK        { Lppterm.Obj($2, Lppterm.Irrelevant) }
  | LBRACK contexted_term RBRACK STAR   { Lppterm.Obj($2, Lppterm.Smaller) }
  | LBRACK contexted_term RBRACK AT     { Lppterm.Obj($2, Lppterm.Equal) }

top_command :
  | THEOREM ID COLON lppterm DOT        { Prover.Theorem($2, $4) }
  | THEOREM lppterm DOT                 { Prover.Theorem("Goal", $2) }
  | EOF                                 { raise End_of_file }
