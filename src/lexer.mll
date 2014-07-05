(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

{
  open Parser
  open Lexing

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }

  let comment_level = ref 0
}

let number = ['0'-'9'] +

(* Initial characters for variables *)
let ichar = ['A'-'Z' 'a'-'z' '-' '^' '=' '`' '\'' '?' '$' '~']

(* Characters allowed only in the body of variables. *)
let bchar = ['0'-'9' '_' '/' '*' '@' '+' '#' '!' '&']

let name = ichar (ichar|bchar)*
let blank = ' ' | '\t' | '\r'

rule token = parse
| "/*"               { incr comment_level; comment lexbuf }
| "%:" (name as s) ":" [^'\n']* '\n'
                     { incrline lexbuf; CLAUSENAME s }
| '%' [^'\n']* '\n'? { incrline lexbuf; token lexbuf }

| blank              { token lexbuf }
| '\n'               { incrline lexbuf; token lexbuf }

| '"' ([^ '"']* as s) '"'
                     { QSTRING s }

| "kind"             { KIND }
| "type"             { TYPE }
| "Kind"             { KKIND }
| "Type"             { TTYPE }
| "Close"            { CLOSE }
| "sig"              { SIG }
| "module"           { MODULE }
| "accum_sig"        { ACCUMSIG }
| "accumulate"       { ACCUM }
| "end"              { END }

| "=>"               { IMP }
| "<="               { IF }
| ":-"               { CLAUSEEQ }
| ":="               { DEFEQ }
| ","                { COMMA }
| "."                { DOT }
| ";"                { SEMICOLON }
| "\\"               { BSLASH }
| "("                { LPAREN }
| ")"                { RPAREN }
| "|-"               { TURN }
| "::"               { CONS }
| "="                { EQ }

| ":"                { COLON }
| "->"               { RARROW }
| "forall"           { FORALL }
| "nabla"            { NABLA }
| "exists"           { EXISTS }
| "*"                { STAR }
| "@"                { AT }
| "#"                { HASH }
| "+"                { PLUS }
| "Theorem"          { THEOREM }
| "Define"           { DEFINE }
| "CoDefine"         { CODEFINE }
| "Query"            { QUERY }
| "Import"           { IMPORT }
| "Specification"    { SPECIFICATION }
| "Split"            { SSPLIT }
| "\\/"              { OR }
| "/\\"              { AND }
| "{"                { LBRACE }
| "}"                { RBRACE }
| "["                { LBRACK }
| "]"                { RBRACK }
| "true"             { TRUE }
| "false"            { FALSE }

| "induction"        { IND }
| "coinduction"      { COIND }
| "apply"            { APPLY }
| "backchain"        { BACKCHAIN }
| "inst"             { INST }
| "cut"              { CUT }
| "from"             { FROM }
| "case"             { CASE }
| "search"           { SEARCH }
| "to"               { TO }
| "with"             { WITH }
| "on"               { ON }
| "by"               { BY }
| "as"               { AS }
| "witness"          { WITNESS }
| "split"            { SPLIT }
| "split*"           { SPLITSTAR }
| "left"             { LEFT }
| "right"            { RIGHT }
| "unfold"           { UNFOLD }
| "intros"           { INTROS }
| "skip"             { SKIP }
| "abort"            { ABORT }
| "undo"             { UNDO }
| "assert"           { ASSERT }
| "keep"             { KEEP }
| "clear"            { CLEAR }
| "abbrev"           { ABBREV }
| "unabbrev"         { UNABBREV }
| "monotone"         { MONOTONE }
| "permute"          { PERMUTE }
| "rename"           { RENAME }

| "Set"              { SET }
| "Show"             { SHOW }
| "Quit"             { QUIT }

| "_"                { UNDERSCORE }
| number as n        { NUM (int_of_string n) }
| name as n          { STRINGID n }

| eof                { EOF }

| '\x04'             { EOF }   (* ctrl-D *)

| _                  { failwith ("Illegal character " ^
                                   (Lexing.lexeme lexbuf) ^ " in input") }

and comment = parse
| [^ '*' '/' '\n']+  { comment lexbuf }
| "/*"               { incr comment_level; comment lexbuf }
| "*/"               { decr comment_level ;
                       if !comment_level = 0 then
                         token lexbuf
                       else
                         comment lexbuf }
| "*"                { comment lexbuf }
| "/"                { comment lexbuf }
| "\n"               { incrline lexbuf; comment lexbuf }
| eof                { print_endline
                         "Warning: comment not closed at end of file" ;
                       token lexbuf }
