%{
  let strip_brackets str =
    String.sub str 1 ((String.length str) - 2)
    
  let parse_contexted_term str =
    let str = strip_brackets str in
      Parser.contexted_term Lexer.token (Lexing.from_string str)
%}

%token COMMA DOT COLON RARROW FORALL EXISTS STAR AT THEOREM OR
%token LPAREN RPAREN
%token <string> ID
%token <string> TERM
%token EOF

%start lppterm top_command
%type <Lppterm.lppterm> lppterm
%type <Prover.top_command> top_command

  
/* Lower */
  
%nonassoc COMMA
%right RARROW
%left OR
  
/* Higher */
  
%%

lppterm:
  | FORALL binding_list COMMA lppterm { Lppterm.Forall($2, $4) }
  | EXISTS binding_list COMMA lppterm { Lppterm.Exists($2, $4) }
  | lppterm RARROW lppterm            { Lppterm.Arrow($1, $3) }
  | lppterm OR lppterm                { Lppterm.Or($1, $3) }
  | LPAREN lppterm RPAREN             { $2 }
  | object_term                       { $1 }

binding_list:
  | binding binding_list              { $1::$2 }
  | binding                           { [$1] }

binding:
  | ID                                { $1 }

object_term:
  | TERM                              { Lppterm.Obj(parse_contexted_term $1,
                                                    Lppterm.Irrelevant) }
  | TERM STAR                         { Lppterm.Obj(parse_contexted_term $1,
                                                    Lppterm.Smaller) }
  | TERM AT                           { Lppterm.Obj(parse_contexted_term $1,
                                                    Lppterm.Equal) }

top_command :
  | THEOREM ID COLON lppterm DOT      { Prover.Theorem($2, $4) }
  | THEOREM lppterm DOT               { Prover.Theorem("Goal", $2) }
  | EOF                               { raise End_of_file }
