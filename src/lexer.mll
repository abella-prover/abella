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
let name = ['A' - 'Z' 'a'-'z' '_' '/' '0'-'9' '\'' '?' '-' '`' '#' '$' '&' '!' '~'] +
let blank = ' ' | '\t' | '\r'

rule token = parse
| "/*"               { incr comment_level; comment lexbuf }
| '%' [^'\n']* '\n'  { incrline lexbuf; token lexbuf }

| blank              { token lexbuf }
| '\n'               { incrline lexbuf; token lexbuf }

| '"' ([^ '"']* as s) '"'
                     { QSTRING s }

| "=>"               { IMP }
| ":-"               { CLAUSEEQ }
| ":="               { DEFEQ }
| ","                { COMMA }
| "."                { DOT }
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
| "+"                { PLUS }
| "Theorem"          { THEOREM }
| "Define"           { DEFINE }
| "CoDefine"         { CODEFINE }
| "\\/"              { OR }
| "/\\"              { AND }
| "{"                { LBRACK }
| "}"                { RBRACK }
| "true"             { TRUE }
| "false"            { FALSE }

| "induction"        { IND }
| "coinduction"      { COIND }
| "apply"            { APPLY }
| "inst"             { INST }
| "cut"              { CUT }
| "case"             { CASE }
| "search"           { SEARCH }
| "to"               { TO }
| "with"             { WITH }
| "on"               { ON }
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

| "Set"              { SET }

| number as n        { NUM (int_of_string n) }
| name as n          { STRINGID n }

| eof                { EOF }

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
