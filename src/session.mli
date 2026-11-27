(****************************************************************************)
(* Copyright (C) 2013-2026 Inria (Institut National de Recherche            *)
(*                                en Informatique et en Automatique)        *)
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

(** Stateful, undo-enabled, JSON-collecting prover sessions. *)

open Extensions

type name_mode = [`relaxed | `warn | `strict]

type start_pos = {
  offset : int ;
  line : int ;
  bol : int ;
}

type outcome = {
  ok : bool ;
  messages : Json.t list ;
}

type command_chunk = {
  text : string ;
  start : start_pos ;
  end_line : int ;
  end_col : int ;
}

val system_message : severity:string -> string -> Json.t

val init :
  ?files:(string * string) list ->
  ?strict:bool ->
  ?name_mode:name_mode ->
  ?thc_cache_limit:int ->
  ?trust_compiled:bool ->
  ?welcome:bool ->
  root:string ->
  unit ->
  outcome

val process : ?start:start_pos -> string -> outcome
val back : int -> outcome
val try_command : ?start:start_pos -> string -> outcome

val current_state : unit -> Json.t option
val current_display : unit -> string
val in_proof : unit -> bool

val split_commands : ?filename:string -> string -> command_chunk list
