{
  open Parser
  open Lexing

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }
}

let number = ['0'-'9'] +
let name = ['A' - 'Z' 'a'-'z' '_' '/' '0'-'9' '\''] +
let blank = ' ' | '\t' | '\r'

rule token = parse
| '%' [^'\n'] * '\n' { incrline lexbuf; token lexbuf }
| blank              { token lexbuf }
| '\n'               { incrline lexbuf; token lexbuf }

| "," { COMMA }
| ":" { COLON }      
| "{" { LBRACKET }
| "}" { RBRACKET }
| "=>" { IMP }
| ":-" { DEF }
| "." { DOT }
| "->" { RARROW }
| "forall" { FORALL }
| "\\" { BSLASH }
| "(" { LPAREN }
| ")" { RPAREN }
| "*" { STAR }
| "@" { AT }
      
| "induction" { IND }
| "apply" { APPLY }
| "case" { CASE }
| "search" { SEARCH }
| "to" { TO }
| "on" { ON }
| "and" { AND }
| "Theorem" { THEOREM }
| "intros" { INTROS }

| number as n { NUM (int_of_string n) }
| name as n { ID n }

| eof    { EOF }
