(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

let version = "2.0.9 DAMF"

module Json = Yojson.Safe

let read_all ic =
  let len = 64 in
  let byte_buf = Bytes.create len in
  let buf = Buffer.create 19 in
  let rec spin () =
    match Stdlib.input ic byte_buf 0 len with
    | 0 -> ()                   (* EOF reached *)
    | n ->
        Buffer.add_subbytes buf byte_buf 0 n ;
        spin ()
  in
  spin () ; Buffer.contents buf

let setoff prefix str =
  String.split_on_char '\n' str |>
  List.map (fun line -> prefix ^ line) |>
  String.concat "\n"

let run_command cmd go =
  let cmd = cmd ^ " 2>&1" in
  let (outc, inc) as proc = Unix.open_process cmd in
  go inc ;
  close_out inc ;
  match Unix.waitpid [] (Unix.process_pid proc) with
  | (_, Unix.WEXITED 0) ->
      read_all outc
  | _ | exception _ ->
      Printf.eprintf "Error in subprocess\nCommand: \"%s\"\n%s\n%!"
        cmd
        (setoff "> " (read_all outc)) ;
      failwith "Error in subprocess"

let () =
  let output_file = ref "" in
  let options = Arg.align [
      "-o", Set_string output_file, "FILE Set output to FILE"
    ] in
  let usage_message = Printf.sprintf "%s -o FILE"
      (Filename.basename Sys.executable_name) in
  Arg.parse options (fun _ -> failwith "bad arguments") usage_message ;
  if !output_file = "" then
    failwith "Needs an output file" ;
  let tool_json : Json.t = `Assoc [
      "name", `String "Abella" ;
      "version", `String version ;
      "tag", `String ("Abella " ^ version) ;
    ] in
  let cid =
    run_command "ipfs dag put" (fun oc -> Json.to_channel oc tool_json) |>
    String.trim in
  let tool_json : Json.t = `Assoc [
      "format", `String "tool" ;
      "content", `Assoc [ "/", `String cid ]
    ] in
  let tool_cid = String.trim @@ run_command "ipfs dag put" (fun oc -> Json.to_channel oc tool_json) in
  let lang_json : Json.t = `Assoc [
      "name", `String "Abella" ;
      "version", `String version ;
      "tag", `String ("Abella " ^ version) ;
    ] in
  let cid =
    run_command "ipfs dag put" (fun oc -> Json.to_channel oc lang_json) |>
    String.trim in
  let lang_json : Json.t = `Assoc [
      "format", `String "language" ;
      "content", `Assoc [ "/", `String cid ]
    ] in
  let lang_cid = String.trim @@ run_command "ipfs dag put" (fun oc -> Json.to_channel oc lang_json) in
  let oc = open_out !output_file in
  Printf.fprintf oc "(* This file is generated. Do not edit! *)\n" ;
  Printf.fprintf oc "(* dune exec ../gen/damf_cids.ml -- -o damf_cids.ml *)\n" ;
  Printf.fprintf oc "let language_cid = \"%s\";;\n" lang_cid ;
  Printf.fprintf oc "let tool_cid = \"%s\";;\n" tool_cid ;
  close_out oc
