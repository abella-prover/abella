%token IMP DEF COMMA DOT BSLASH LPAREN RPAREN TURN CONS EQ
%token IND INST APPLY CASE SEARCH TO ON WITH INTROS CUT ASSERT
%token SKIP UNDO ABORT
%token SPLIT SPLITSTAR UNFOLD KEEP CLEAR
%token THEOREM AXIOM DEF
%token COLON RARROW FORALL NABLA EXISTS STAR AT OR AND LBRACK RBRACK

%token <int> NUM
%token <string> ID
%token EOF

/* Lower */
  
%nonassoc COMMA
%right RARROW
%left OR
%left AND
  
%right CONS

%nonassoc BSLASH
%right IMP
%nonassoc EQ

/* Higher */


%start metaterm term clauses top_command command contexted_term meta_clause
%start meta_clauses
%type <Term.term> term
%type <Types.clauses> clauses
%type <Types.meta_clause> meta_clause
%type <Types.meta_clauses> meta_clauses
%type <Types.command> command
%type <Metaterm.obj> contexted_term
%type <Metaterm.metaterm> metaterm
%type <Types.top_command> top_command

%%

contexted_term:
  | context TURN term                   { Metaterm.context_obj $1 $3 }
  | term                                { Metaterm.obj $1 }

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

meta_clauses:
  | meta_clause meta_clauses            { $1::$2 }
  |                                     { [] }

meta_clause:
  | metaterm DOT                        { ($1, []) }
  | metaterm DEF meta_clause_body DOT   { ($1, $3) }

meta_clause_body:
  | metaterm COMMA meta_clause_body     { $1::$3 }
  | metaterm                            { [$1] }


command:
  | IND ON NUM DOT                      { Types.Induction($3) }
  | APPLY ID TO id_list DOT             { Types.Apply($2, $4) }
  | CUT ID WITH ID DOT                  { Types.Cut($2, $4) }
  | INST ID WITH ID EQ term DOT         { Types.Inst($2, $4, $6) }
  | CASE ID DOT                         { Types.Case($2, false) }
  | CASE ID LPAREN KEEP RPAREN DOT      { Types.Case($2, true) }
  | ASSERT metaterm DOT                 { Types.Assert($2) }
  | EXISTS term DOT                     { Types.Exists($2) }
  | SEARCH DOT                          { Types.Search }
  | SPLIT DOT                           { Types.Split }
  | SPLITSTAR DOT                       { Types.SplitStar }
  | INTROS DOT                          { Types.Intros }
  | SKIP DOT                            { Types.Skip }
  | ABORT DOT                           { Types.Abort }
  | UNDO DOT                            { Types.Undo }
  | UNFOLD DOT                          { Types.Unfold }
  | CLEAR id_list DOT                   { Types.Clear($2) }
  | EOF                                 { raise End_of_file }

id_list:
  | ID id_list                          { $1::$2 }
  | ID                                  { [$1] }

metaterm:
  | FORALL binding_list COMMA metaterm  { Metaterm.forall $2 $4 }
  | EXISTS binding_list COMMA metaterm  { Metaterm.exists $2 $4 }
  | NABLA binding_list COMMA metaterm   { Metaterm.nabla $2 $4 }
  | metaterm RARROW metaterm            { Metaterm.arrow $1 $3 }
  | metaterm OR metaterm                { Metaterm.meta_or $1 $3 }
  | metaterm AND metaterm               { Metaterm.meta_and $1 $3 }
  | LPAREN metaterm RPAREN              { $2 }
  | LBRACK contexted_term RBRACK restriction
                                        { Metaterm.Obj($2, $4) }
  | term restriction                    { Metaterm.Pred($1, $2) }

binding_list:
  | binding binding_list                { $1::$2 }
  | binding                             { [$1] }

binding:
  | ID                                  { $1 }

restriction:
  |                                     { Metaterm.Irrelevant }
  | stars                               { Metaterm.Smaller $1 }
  | ats                                 { Metaterm.Equal $1 }
      
stars:
  | STAR stars                          { 1 + $2 }
  | STAR                                { 1 }
      
ats:
  | AT ats                              { 1 + $2 }
  | AT                                  { 1 }
      
top_command :
  | THEOREM ID COLON metaterm DOT       { Types.Theorem($2, $4) }
  | THEOREM metaterm DOT                { Types.Theorem("Goal", $2) }
  | AXIOM ID COLON metaterm DOT         { Types.Axiom($2, $4) }
  | DEF meta_clause                     { Types.Def($2) }
  | EOF                                 { raise End_of_file }
