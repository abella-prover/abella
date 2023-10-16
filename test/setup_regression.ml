(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(*
Set up the regression testing permissions by:

  - setting directories to be writable
  - removing .thc and .out files
*)

let actual = ref false

let options = Arg.[
    "--actual", Set actual, " actually run the regression suite"
  ] |> Arg.align

let examples_dir = ref None

let set_examples_dir dir =
  match Unix.stat dir with
  | { st_kind = S_DIR ; _ } ->
      examples_dir := Some dir
  | _
  | exception _ ->
      failwith ("Cannot find dir: " ^ dir)

let rec process dir =
  Unix.chmod dir 0o755 ;
  let fs = Sys.readdir dir in
  Array.fast_sort String.compare fs ;
  Array.iter begin fun file ->
    let file = Filename.concat dir file in
    match Unix.stat file with
    | { st_kind = S_DIR ; _ } ->
        process file
    | { st_kind = S_REG ; _ } -> begin
        if List.exists (fun suffix -> String.ends_with ~suffix file) [
            ".thc" ; ".out"
          ] then Unix.unlink file
      end
    | _ -> ()
  end fs

let main () =
  Arg.parse options set_examples_dir "" ;
  if not !actual then () else
  match !examples_dir with
  | None ->
      failwith "Missing required argument"
  | Some dir ->
      process dir

let () =
  if not !Sys.interactive then
    try main () with
    | ex ->
        let msg = match ex with
          | Failure msg -> msg
          | _ -> Printexc.to_string ex
        in
        Printf.eprintf "Failure: %s\n%!" msg ;
        exit 1
