%token BSLASH LPAREN RPAREN
%token FORALL IMP RARROW COLON COMMA
%token LBRACKET RBRACKET
%token <string> ID
%token EOF

%nonassoc BSLASH
%right IMP

%start lppterm term
%type <Lppterm.lppterm> lppterm
%type <Term.term> term

%%

lppterm:
  | FORALL binding_list COMMA lppterm { Lppterm.forall $2 $4 }
  | object_term RARROW lppterm        { Lppterm.arrow $1 $3 }
  | object_term                       { $1 }

binding_list:
  | binding binding_list              { $1::$2 }
  | binding                           { [$1] }

binding:
  | LPAREN ID COLON term RPAREN       { ($2, $4) }

object_term:
  | LBRACKET term RBRACKET            { Lppterm.obj $2 }

term:
  | term IMP term                     { Term.app (Term.atom "=>") [$1; $3] }
  | ID BSLASH term                    { Term.abstract $1 $3 }
  | exp exp_list                      { Term.app $1 $2 }
  | exp                               { $1 }
      
exp:
  | LPAREN term RPAREN                { $2 }
  | ID                                { Term.atom $1 }
      
exp_list:
  | exp exp_list                      { $1::$2 }
  | exp                               { [$1] }
  | ID BSLASH term                    { [Term.abstract $1 $3] }
