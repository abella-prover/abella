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

open struct
  [@@@warning "-32-38"]

  exception Fail

  let lex source path with_positions =
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
        let lex with_positions = lex source path with_positions
      end in
      (module Source : SOURCE)
    end

  let openers = [
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

module type THM = sig
  include SOURCE

  val out_path : string

  val thc_path : string
  val is_stale : bool
  val marshal : 'a -> unit
  val close : unit -> unit
end

let read_thm ?thc source =
  let module Thm = struct
    include (val read source : SOURCE)
    let base =
      if not @@ Filename.check_suffix path ".thm" then
        Base64.encode path
        |> Result.get_ok
        |> Filename.concat Xdg.cache_dir
      else
        Filename.chop_suffix path ".thm"
    let out_path = base ^ ".out"
    let thc_path = Option.value thc
        ~default:(base ^ ".thc")
    let thc_mtime =
      if Sys.file_exists thc_path then
        Unix.((stat thc_path).st_mtime)
      else 0.
    let is_stale = thc_mtime < mtime
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
          [%bug] "Repeated close() of sink for: %s" path ;
  end in
  (module Thm : THM)
