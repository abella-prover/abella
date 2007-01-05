(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006 David Baelde, Alwen Tiu, Axelle Ziegler               *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

{
  open Parser
  open Lexing

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }
}

let name = ['A' - 'Z' 'a'-'z' '_' '/' '0'-'9' '\''] +
let blank = ' ' | '\t' | '\r'
let instring = [^'"'] *

rule token = parse
| '%' [^'\n'] * '\n' { incrline lexbuf; token lexbuf }
| blank              { token lexbuf }
| '\n'               { incrline lexbuf; token lexbuf }

| "." { DOT }
| "#" { SHARP }
| "=" { EQ }
| ":=" { DEF }
| "," { AND }
| "&" { AND }
| ";" { OR }
| "=>" { IMP }
| "->" { RARROW }
| "<-" { LARROW }
| "+" { PLUS }
| "-" { MINUS }
| "*" { TIMES }
| "\\" { BSLASH }
| "(" { LPAREN }
| ")" { RPAREN }

| "inductive"   { IND   }
| "coinductive" { COIND }

| name as n { ID n }
| '"' (instring as n) '"'
    { String.iter (function '\n' -> incrline lexbuf | _ -> ()) n ;
      STRING n }

| eof    { failwith "eof" }
