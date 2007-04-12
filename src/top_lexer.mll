{
  open Top_parser
  open Lexing

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }
}

let name = ['A' - 'Z' 'a'-'z' '_' '/' '0'-'9' '\''] +
let blank = ' ' | '\t' | '\r'
let term = '{' [^ '}'] + '}'

rule token = parse
| '%' [^'\n'] * '\n' { incrline lexbuf; token lexbuf }
| blank              { token lexbuf }
| '\n'               { incrline lexbuf; token lexbuf }

| ","                { COMMA }
| "."                { DOT }
| ":"                { COLON }
| "->"               { RARROW }
| "forall"           { FORALL }
| "*"                { STAR }
| "@"                { AT }
| "Theorem"          { THEOREM }
| "or"               { OR }
      
| "("                { LPAREN }
| ")"                { RPAREN }

| name as n          { ID n }
| term as s          { TERM s }

| eof                { EOF }
