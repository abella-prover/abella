(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Extensions

let load_path = State.rref ""

let normalize ~wrt fn =
  if Filename.is_relative fn then
    Filename.concat (Filename.dirname wrt) fn
  else if Filename.is_implicit fn then
    Filename.concat !load_path fn
  else fn

let set_load_path ?wrt path =
  load_path :=
    match wrt with
    | None -> path
    | Some wrt -> normalize ~wrt path
