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

(* JS-facing adapter for the wasm_of_ocaml browser target. *)

open Js_of_ocaml
open Abella_lib
open Extensions

let js_string s = Js.Unsafe.inject (Js.string s)
let js_int i = Js.Unsafe.inject (Js.float (float_of_int i))
let js_bool b = Js.Unsafe.inject (Js.bool b)

let rec json_to_js (j : Extensions.Json.t) : Js.Unsafe.any =
  match j with
  | `Null -> Js.Unsafe.inject Js.null
  | `Bool b -> js_bool b
  | `Int i -> js_int i
  | `Intlit s -> js_string s
  | `Float f -> Js.Unsafe.inject (Js.float f)
  | `String s -> js_string s
  | `List items ->
      let items = List.map json_to_js items |> Array.of_list in
      Js.Unsafe.inject (Js.array items)
  | `Assoc fields ->
      let fields =
        List.map (fun (k, v) -> (k, json_to_js v)) fields
        |> Array.of_list
      in
      Js.Unsafe.inject (Js.Unsafe.obj fields)

let result status messages =
  Js.Unsafe.obj [|
    "status", js_string status ;
    "messages", Js.Unsafe.inject begin
      Js.array (List.map json_to_js messages |> Array.of_list)
    end ;
  |]

let outcome_to_js (out : Session.outcome) =
  result (if out.ok then "ok" else "error") out.messages

let error_result message =
  result "error" [Session.system_message ~severity:"error" message]

let field obj name : 'a = Js.Unsafe.get obj (Js.string name)
let int_field obj name = int_of_float (Js.to_float (field obj name))
let item arr i = Js.Unsafe.get arr (Js.float (float_of_int i))

let file_list files =
  let count = int_field files "length" in
  let rec collect i acc =
    if i >= count then List.rev acc
    else begin
      let file = item files i in
      let path = Js.to_string (field file "path") in
      let contents = Js.to_string (field file "contents") in
      let binary = Js.to_bool (field file "binary") in
      let contents =
        if binary then
          match Base64.decode contents with
          | Ok bytes -> bytes
          | Error (`Msg msg) ->
              failwithf "Invalid base64 contents for %S: %s" path msg
        else contents
      in
      collect (i + 1) ((path, contents) :: acc)
    end
  in
  collect 0 []

let name_mode_of_js mode : Session.name_mode =
  match Js.to_string mode with
  | "warn" -> `warn
  | "strict" -> `strict
  | _ -> `relaxed

let init files root strict name_mode =
  try
    let files = file_list files in
    let root = Js.to_string root in
    let strict = Js.to_bool strict in
    let name_mode = name_mode_of_js name_mode in
    outcome_to_js (Session.init ~files ~strict ~name_mode ~root ())
  with e -> error_result (Printexc.to_string e)

let reset = init

let process command start =
  try
    let command = Js.to_string command in
    let start : Session.start_pos = {
      offset = int_field start "offset" ;
      line = int_field start "line" ;
      bol = int_field start "bol" ;
    } in
    outcome_to_js (Session.process ~start command)
  with e ->
    error_result (sorry e)

let back count =
  outcome_to_js (Session.back count)

(* Phase 0 helper: the generated .thc bytes for a virtual file, base64. *)
let thc path =
  try
    let path = Js.to_string path in
    if Source.virtual_exists path then
      Js.Unsafe.inject
        (Js.string (Base64.encode_exn (Source.virtual_contents path)))
    else
      Js.Unsafe.inject Js.null
  with _ -> Js.Unsafe.inject Js.null

(* Install the progress callback used by the worker. *)
let set_on_import callback =
  Driver.Setup.on_import := Some (fun name ->
      try
        ignore (Js.Unsafe.fun_call callback
                  [| Js.Unsafe.inject (Js.string name) |])
      with Js_error.Exn _ as e ->
        failwithf "Import progress callback failed: %s"
          (Printexc.to_string e))

let () =
  let api = Js.Unsafe.obj [|
    "init", Js.Unsafe.inject (Js.Unsafe.callback init) ;
    "reset", Js.Unsafe.inject (Js.Unsafe.callback reset) ;
    "process", Js.Unsafe.inject (Js.Unsafe.callback process) ;
    "back", Js.Unsafe.inject (Js.Unsafe.callback back) ;
    "thc", Js.Unsafe.inject (Js.Unsafe.callback thc) ;
    "setOnImport", Js.Unsafe.inject (Js.Unsafe.callback set_on_import) ;
  |] in
  Js.Unsafe.set Js.Unsafe.global (Js.string "Abellajs") api ;
  Js.export "Abellajs" api
