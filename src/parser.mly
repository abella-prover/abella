%token IMP DEF COMMA DOT BSLASH LPAREN RPAREN TURN CONS EQ
%token IND INST APPLY CASE SEARCH TO ON WITH INTROS SKIP UNDO CUT ASSERT
%token THEOREM AXIOM DEF
%token COLON RARROW FORALL EXISTS STAR AT OR LBRACK RBRACK

%token <int> NUM
%token <string> ID
%token EOF

/* Lower */
  
%nonassoc COMMA
%right RARROW
%left OR
  
%right CONS

%nonassoc BSLASH
%right IMP
%nonassoc EQ

/* Higher */


%start lppterm term clauses top_command command contexted_term
%type <Term.term> term
%type <Types.clauses> clauses
%type <Types.command> command
%type <Lppterm.obj> contexted_term
%type <Lppterm.lppterm> lppterm
%type <Types.top_command> top_command

%%

contexted_term:
  | context TURN term                   { Lppterm.context_obj $1 $3 }
  | term                                { Lppterm.obj $1 }

context:
  | context COMMA term                  { Context.add $3 $1 }
  | term                                { Context.add $1 Context.empty }
      
term:
  | term IMP term                       { Term.binop "=>" $1 $3 }
  | term CONS term                      { Term.binop "::" $1 $3 }
  | term EQ term                        { Term.binop "=" $1 $3 }
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
  | IND ON NUM DOT                      { Types.Induction($3) }
  | APPLY ID TO id_list DOT             { Types.Apply($2, $4) }
  | CUT ID WITH ID DOT                  { Types.Cut($2, $4) }
  | INST ID WITH ID EQ term DOT         { Types.Inst($2, $4, $6) }
  | CASE ID DOT                         { Types.Case($2) }
  | ASSERT lppterm DOT                  { Types.Assert($2) }
  | SEARCH DOT                          { Types.Search }
  | INTROS DOT                          { Types.Intros }
  | SKIP DOT                            { Types.Skip }
  | UNDO DOT                            { Types.Undo }
  | EOF                                 { raise End_of_file }

id_list:
  | ID id_list                          { $1::$2 }
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
  | LBRACK contexted_term RBRACK stars  { Lppterm.Obj($2, Lppterm.Smaller $4) }
  | LBRACK contexted_term RBRACK ats    { Lppterm.Obj($2, Lppterm.Equal $4) }

stars:
  | STAR stars                          { 1 + $2 }
  | STAR                                { 1 }
      
ats:
  | AT ats                              { 1 + $2 }
  | AT                                  { 1 }
      
top_command :
  | THEOREM ID COLON lppterm DOT        { Types.Theorem($2, $4) }
  | THEOREM lppterm DOT                 { Types.Theorem("Goal", $2) }
  | AXIOM ID COLON lppterm DOT          { Types.Axiom($2, $4) }
  | DEF clause                          { Types.Def($2) }
  | EOF                                 { raise End_of_file }
