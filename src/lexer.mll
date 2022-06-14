(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2022 Inria (Institut National de Recherche            *)
(*                         en Informatique et en Automatique)               *)
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

  let keyword_table : (string, token) Hashtbl.t = Hashtbl.create 89 ;;
  let () = List.iter (fun (k, t) -> Hashtbl.add keyword_table k t) [
    "Close",         CLOSE ;
    "CoDefine",      CODEFINE ;
    "Define",        DEFINE ;
    "Import",        IMPORT ;
    "Kind",          KKIND ;
    "Query",         QUERY ;
    "Quit",          QUIT ;
    "Set",           SET ;
    "Show",          SHOW ;
    "Specification", SPECIFICATION ;
    "Split",         SSPLIT ;
    "Theorem",       THEOREM ;
    "Type",          TTYPE ;
    "abbrev",        ABBREV ;
    "abort",         ABORT ;
    "accum_sig",     ACCUMSIG ;
    "accumulate",    ACCUM ;
    "all",           ALL ;
    "apply",         APPLY ;
    "as",            AS ;
    "assert",        ASSERT ;
    "async",         ASYNC ;
    "backchain",     BACKCHAIN ;
    "by",            BY ;
    "case",          CASE ;
    "clear",         CLEAR ;
    "coinduction",   COIND ;
    "cut",           CUT ;
    "end",           END ;
    "exists",        EXISTS ;
    "false",         FALSE ;
    "forall",        FORALL ;
    "from",          FROM ;
    "induction",     IND ;
    "inst",          INST ;
    "intros",        INTROS ;
    "keep",          KEEP ;
    "kind",          KIND ;
    "left",          LEFT ;
    "module",        MODULE ;
    "monotone",      MONOTONE ;
    "nabla",         NABLA ;
    "on",            ON ;
    "permute",       PERMUTE ;
    "rename",        RENAME ;
    "right",         RIGHT ;
    "search",        SEARCH ;
    "sig",           SIG ;
    "skip",          SKIP ;
    "split",         SPLIT ;
    "split*",        SPLITSTAR ;
    "to",            TO ;
    "true",          TRUE ;
    "type",          TYPE ;
    "unabbrev",      UNABBREV ;
    "undo",          UNDO ;
    "unfold",        UNFOLD ;
    "with",          WITH ;
    "witness",       WITNESS ;
  ] ;;

  let comment_level = ref 0
}

let number = ['0'-'9'] +

(* Initial characters for variables *)
let ichar = ['A'-'Z' 'a'-'z' '-' '^' '=' '`' '\'' '?' '$']

(* Characters allowed only in the body of variables. *)
let bchar = ['0'-'9' '_' '/' '*' '@' '+' '#' '!' '~']

let name = ichar (ichar|bchar)*
let blank = ' ' | '\t' | '\r'

rule token = parse
| "/*"               { incr comment_level; comment lexbuf }
| "%:" (name as s) ":" [^'\n']* '\n'
                     { Lexing.new_line lexbuf; CLAUSENAME s }
| '%' [^'\n']* '\n'? { Lexing.new_line lexbuf; token lexbuf }

| blank              { token lexbuf }
| '\n'               { Lexing.new_line lexbuf; token lexbuf }

| '"' ([^ '"']* as s) '"'
                     { QSTRING s }

| "#back"            { BACK }
| "#reset"           { RESET }

| "=>"               { IMP }
| "<="               { IF }
| "&"                { AMP }
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
| "*"                { STAR }
| "@"                { AT }
| "#"                { HASH }
| "+"                { PLUS }
| "\\/"              { OR }
| "/\\"              { AND }
| "{"                { LBRACE }
| "}"                { RBRACE }
| "["                { LBRACK }
| "]"                { RBRACK }

| "_"                { UNDERSCORE }
| number as n        { NUM (int_of_string n) }
| name as id          { try Hashtbl.find keyword_table id
                       with Not_found -> STRINGID id }

| eof                { EOF }

| '\x04'             { EOF }   (* ctrl-D *)

| _                  {
    let open Lexing in
    let pos = lexeme_start_p lexbuf in
    let msg = "Illegal character '" ^ String.escaped (lexeme lexbuf) ^ "' in input" in
    let msg = match pos.pos_fname with
      | "" -> msg
      | fname -> Printf.sprintf "File %S, line %d, character %d: %s"
                   fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol) msg
    in
    failwith msg
  }

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
| "\n"               { Lexing.new_line lexbuf; comment lexbuf }
| eof                { print_endline
                         "Warning: comment not closed at end of file" ;
                       token lexbuf }
