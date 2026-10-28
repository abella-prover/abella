(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                            en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Session configuration and state shared by the driver and the
   file-kind-specific modules. *)

open Abella_types

let compiled : (module Source.COMPILED) option ref = ref None
let mode : [`batch | `interactive] ref = ref `interactive
let annotate : bool ref = ref true
let recurse : bool ref = ref false
let input : string ref = ref "" (* file name including suffix *)
let lexbuf : Lexing.lexbuf ref = ref (Lexing.from_string "")
let unfinished : string list ref = State.rref []
let axioms : string list ref = State.rref []
let import_mode : [`thc | `source | `auto] ref = ref `thc
let trust_compiled : bool ref = ref false
let file_kind : [`thm | `thmod] ref = Typing.file_kind

let witnesses = State.rref false

exception UserInterrupt
exception AbellaExit of int

(* Specification clauses stored in both .thc and .thmodc artifacts.  Only
   .thm developments can read a specification, so this is normally empty
   for .thmod files. *)
let spec_sign : Typing.sign ref = State.rref ([], [])
let spec_clauses : clause list ref = State.rref []

let on_import : (string -> unit) option ref = ref None

(* Files currently being source-compiled, outermost first. *)
let compiling : string list ref = ref []

type saved = {
  snapshot : State.snap ;
  mode : [`batch | `interactive] ;
  annotate : bool ;
  recurse : bool ;
  input : string ;
  lexbuf : Lexing.lexbuf ;
  compiled : (module Source.COMPILED) option ;
  import_mode : [`thc | `source | `auto] ;
  trust_compiled : bool ;
  file_kind : [`thm | `thmod] ;
  on_import : (string -> unit) option ;
  compiling : string list ;
  dest : Output.t ;
  undo : bool ;
}

let save () = {
  snapshot = State.snapshot () ;
  mode = !mode ;
  annotate = !annotate ;
  recurse = !recurse ;
  input = !input ;
  lexbuf = !lexbuf ;
  compiled = !compiled ;
  import_mode = !import_mode ;
  trust_compiled = !trust_compiled ;
  file_kind = !file_kind ;
  on_import = !on_import ;
  compiling = !compiling ;
  dest = !Output.dest ;
  undo = State.Undo.is_enabled () ;
}

let restore saved =
  State.reload saved.snapshot ;
  mode := saved.mode ;
  annotate := saved.annotate ;
  recurse := saved.recurse ;
  input := saved.input ;
  lexbuf := saved.lexbuf ;
  compiled := saved.compiled ;
  import_mode := saved.import_mode ;
  trust_compiled := saved.trust_compiled ;
  file_kind := saved.file_kind ;
  on_import := saved.on_import ;
  compiling := saved.compiling ;
  Output.dest := saved.dest ;
  State.Undo.set_enabled saved.undo

let with_saved f =
  let saved = save () in
  Fun.protect ~finally:(fun () -> restore saved) f
