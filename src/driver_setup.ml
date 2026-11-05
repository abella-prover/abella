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
let mode : [`batch | `interactive | `switch] ref = ref `interactive
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

let initial_snapshot : State.snap option ref = ref None

(* The driver loop is installed here to avoid a dependency cycle between
   the driver and the file-kind-specific modules. *)
let process1 : (unit -> [`ok | `error]) ref = ref (fun () -> `ok)

type processing_state =
  | Process_top
  | Process_proof of proof_processor

and proof_processor = {
  thm_id : int ;
  thm : string ;
  compile : fin -> unit ;
  reset : (unit -> unit) ;
}

let current_state = State.rref Process_top
