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


let rec pp_uterm ff ut =
  let open Format in
  match ut with
  | UCon (_, s, _) -> fprintf ff "%s" s
  | ULam (_, x, _, ut) ->
      fprintf ff "(@[<b2>%s\\@ %a@])" x pp_uterm ut
  | UApp (_, utf, utx) ->
      fprintf ff "(@[<b2>%a@ %a@])" pp_uterm utf pp_uterm utx
  | UJudge (_, u, j) ->
      fprintf ff "(@[<b2>%a :@ %a@])" pp_uterm u pp_uterm j
  | UPi (_, x, a, b) ->
      fprintf ff "(@[<b2>{%s:%a}@ %a@])" x pp_uterm a pp_uterm b
  | UAbs (_, x, a, b) ->
      fprintf ff "(@[<b2>[%s:%a]@ %a@])" x pp_uterm a pp_uterm b
  | UImp (_, a, b) ->
      fprintf ff "(@[<b2>%a ->@ %a@])" pp_uterm a pp_uterm b
  | UType _ ->
      fprintf ff "type"
