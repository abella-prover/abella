(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions

module type SOURCE = sig
  (** the full name *)
  val path : string

  (** the "directory" where the file is *)
  val dir  : string option

  (** the last modification time *)
  val mtime : float

  (** lexically analyze the file *)
  val lex  : bool -> Lexing.lexbuf
end

module type THM = sig
  include SOURCE

  val out_path : string

  val thc_path : string
  val is_stale : bool
  val marshal : 'a -> unit
  val close : unit -> unit

  (** the bytes of the (possibly generated) .thc file *)
  val thc_contents : unit -> string
end

(* Project-relative virtual file system. Keys are canonicalized so that
   [Filepath.normalize] results ("./name.thm") and bundle keys
   ("name.thm") agree. *)

let canon path =
  let normalize_sep c = if c = '\\' then '/' else c in
  let rec collapse acc = function
    | [] -> List.rev acc
    | "" :: rest
    | "." :: rest -> collapse acc rest
    | ".." :: rest -> begin
        match acc with
        | [] -> collapse (".." :: acc) rest
        | _ :: acc -> collapse acc rest
      end
    | x :: rest -> collapse (x :: acc) rest
  in
  let parts =
    String.split_on_char '/'
      (String.map normalize_sep path)
  in
  match collapse [] parts with
  | [] -> "."
  | parts -> String.concat "/" parts

let virtual_files : (string, string) Hashtbl.t = Hashtbl.create 19

let add_virtual path contents =
  Hashtbl.replace virtual_files (canon path) contents

let virtual_exists path =
  Hashtbl.mem virtual_files (canon path)

let virtual_contents path =
  Hashtbl.find virtual_files (canon path)

let clear_virtual () =
  Hashtbl.clear virtual_files

(* Set when a browser-generated .thc file is ready. *)
let thc_trusted : (string, bool) Hashtbl.t = Hashtbl.create 19

let set_thc_trusted path trusted =
  Hashtbl.replace thc_trusted (canon path) trusted

let is_thc_trusted path =
  Hashtbl.find_opt thc_trusted (canon path) |> Option.value ~default:false

let clear_thc_trust () =
  Hashtbl.clear thc_trusted

open struct
  [@@@warning "-32-38"]

  exception Fail

  let lex_channel source path with_positions =
    let ch = Stdlib.open_in_bin path in
    let lb = Lexing.from_channel ~with_positions ch in
    Lexing.set_filename lb source;
    lb

  let open_local_file =
    Result.wrap begin fun source ->
      let module Source = struct
        let path = source
        let mtime = Unix.((stat source).st_mtime)
        let dir = Some (Filename.dirname path)
        let lex with_positions = lex_channel source path with_positions
      end in
      (module Source : SOURCE)
    end

  let open_virtual_file =
    Result.wrap begin fun source ->
      let path = canon source in
      let contents = Hashtbl.find virtual_files path in
      let module Source = struct
        let path = path
        let mtime = 0.
        let dir = Some (Filename.dirname path)
        let lex _with_positions =
          let lb = Lexing.from_string contents in
          Lexing.set_filename lb path ;
          lb
      end in
      (module Source : SOURCE)
    end

  let openers = [
    "virtual", open_virtual_file ;
    "local", open_local_file ;
  ]
end

let read source =
  let rec spin ops =
    match ops with
    | [] ->
        failwithf "Opening: %s" source
    | (_op_name, op_fn) :: ops ->
        match op_fn source with
        | Ok s -> s
        | Error _exn -> (spin[@tailrec]) ops
  in
  spin openers

let read_file_bytes path =
  let ch = Stdlib.open_in_bin path in
  Fun.protect ~finally:(fun () -> Stdlib.close_in ch) begin fun () ->
    let len = in_channel_length ch in
    really_input_string ch len
  end

let read_thm ?thc source =
  let is_virtual = virtual_exists source in
  let module Thm = struct
    include (val read source : SOURCE)

    let base =
      if is_virtual then
        if Filename.check_suffix path ".thm" then
          Filename.chop_suffix path ".thm"
        else path
      else if not @@ Filename.check_suffix path ".thm" then
        Base64.encode path
        |> Result.get_ok
        |> Filename.concat (Lazy.force Xdg.cache_dir)
      else
        Filename.chop_suffix path ".thm"

    let out_path = base ^ ".out"
    let thc_path = Option.value thc
        ~default:(base ^ ".thc")

    let thc_mtime =
      if not is_virtual && Sys.file_exists thc_path then
        Unix.((stat thc_path).st_mtime)
      else 0.

    let is_stale =
      if is_virtual then not (is_thc_trusted thc_path)
      else thc_mtime < mtime

    let temp = thc_path ^ ".part"
    let channel = ref None

    let marshal thing =
      let ch = match !channel with
        | Some ch -> ch
        | None ->
            let ch = Stdlib.open_out_bin temp in
            channel := Some ch ;
            ch
      in
      Marshal.to_channel ch thing []

    let close () =
      match !channel with
      | Some ch ->
          channel := None ;
          Stdlib.close_out ch ;
          Sys.rename temp thc_path
      | None ->
          [%bug] "Repeated close() of sink for: %s" path

    let thc_contents () =
      if is_virtual then virtual_contents thc_path
      else read_file_bytes thc_path

  end in
  (module Thm : THM)
