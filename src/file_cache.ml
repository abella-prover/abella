(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

let cache : (string, string) Hashtbl.t = Hashtbl.create 19

let add file contents = Hashtbl.add cache file contents

let reset () = Hashtbl.clear cache

let get nm =
  if Hashtbl.mem cache nm then Hashtbl.find cache nm else
  let ch = open_in_bin nm in
  let buf = Buffer.create 19 in
  let () = try begin
    while true do Buffer.add_string buf (input_line ch ^ "\n") done
  end with End_of_file -> () in
  let file_contents = Buffer.contents buf in
  Hashtbl.replace cache nm file_contents ;
  file_contents

let lexbuf filename =
  let lexbuf = Lexing.from_string (get filename) in
  lexbuf.Lexing.lex_curr_p <- {
    lexbuf.Lexing.lex_curr_p with
    Lexing.pos_fname = filename } ;
  lexbuf
