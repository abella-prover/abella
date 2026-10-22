(****************************************************************************)
(* Copyright (C) 2013-2026 Inria (Institut National de Recherche            *)
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

(* JS-facing adapter shared by the js_of_ocaml and wasm_of_ocaml targets. *)

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

let system_message ~severity message : Extensions.Json.t =
  `Assoc [
    "type", `String "system_message" ;
    "id", `Int (-1) ;
    "severity", `String severity ;
    "message", `String message ;
  ]

let result status messages =
  Js.Unsafe.obj [|
    "status", js_string status ;
    "messages", Js.Unsafe.inject begin
      Js.array (List.map json_to_js messages |> Array.of_list)
    end ;
  |]

let error_result message =
  result "error" [system_message ~severity:"error" message]

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

let re_init files root =
  let files = file_list files in
  let root = Js.to_string root in
  State.reload Abella_driver.initial_snapshot ;
  State.Undo.set_enabled true ;
  State.Undo.reset () ;
  Abella_driver.compiling := [] ;
  Accumulate.clear_specification_cache () ;
  Typing.clause_map := Term.Itab.empty ;
  Source.clear_virtual () ;
  Source.clear_thc_trust () ;
  List.iter (fun (path, contents) -> Source.add_virtual path contents) files ;
  Abella_driver.Setup.mode := `interactive ;
  Abella_driver.Setup.annotate := true ;
  Abella_driver.Setup.recurse := false ;
  Abella_driver.Setup.import_mode := `auto ;
  Abella_driver.Setup.trust_compiled := true ;
  Abella_driver.Setup.input := root ;
  Abella_driver.Setup.compiled := None ;
  Abella_driver.Setup.unfinished := [] ;
  Output.collect_mode () ;
  ignore (Output.drain ()) ;
  Output.msg_printf "%s" Abella_driver.welcome_msg ;
  result "ok" (Output.drain ())

let init files root =
  try re_init files root with
  | e -> error_result (Printexc.to_string e)

let reset = init

let process command start =
  try begin
    let command = Js.to_string command in
    let offset = int_field start "offset" in
    let line = int_field start "line" in
    let bol = int_field start "bol" in
    let lb = Lexing.from_string command in
    lb.Lexing.lex_curr_p <- {
      Lexing.pos_fname = !Abella_driver.Setup.input ;
      pos_lnum = line ;
      pos_bol = bol ;
      pos_cnum = offset ;
    } ;
    Abella_driver.Setup.lexbuf := lb ;
    let status =
      try Abella_driver.process1 () with
      | Abella_driver.AbellaExit 0 -> `ok
      | Abella_driver.AbellaExit _ -> `error
      | e ->
          Output.msg_printf ~severity:Error "Error: %s" (sorry e) ;
          `error
    in
    let messages = Output.drain () in
    result (match status with `ok -> "ok" | `error -> "error") messages
  end with
  | e ->
      let messages = Output.drain () in
      result "error" (messages @ [system_message ~severity:"error" (sorry e)])

let back count =
  try begin
    State.Undo.back count ;
    result "ok" (Output.drain ())
  end with
  | e ->
      let messages = Output.drain () in
      result "error" (messages @ [system_message ~severity:"error" (sorry e)])

(* Phase 0 helper: the generated .thc bytes for a virtual file, base64. *)
let thc path =
  let path = Js.to_string path in
  if Source.virtual_exists path then
    Js.Unsafe.inject (Js.string (Base64.encode_exn (Source.virtual_contents path)))
  else
    Js.Unsafe.inject Js.null

(* Install the progress callback used by the worker. *)
let set_on_import callback =
  Abella_driver.on_import := Some (fun name ->
      ignore (Js.Unsafe.fun_call callback
                [| Js.Unsafe.inject (Js.string name) |]))

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
