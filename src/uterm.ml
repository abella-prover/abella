(*
 * Copyright (C) 2014  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Untyped terms *)

open Term

type pos = Lexing.position * Lexing.position

type uterm =
  | UCon of pos * string * ty
  | ULam of pos * string * ty * uterm
  | UApp of pos * uterm * uterm
  | UJudge of pos * uterm * uterm
  | UPi  of pos * string * uterm * uterm
  | UAbs of pos * string * uterm * uterm
  | UImp of pos * uterm * uterm
  | UType of pos
