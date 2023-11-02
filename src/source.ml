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

  let open_local_file source =
    let module Source = struct
      let path = source
      let mtime = Unix.((stat source).st_mtime)
      let dir = Some (Filename.dirname path)
      let lex with_positions =
        Stdlib.open_in_bin path
        |> Lexing.from_channel ~with_positions
    end in
    (module Source : SOURCE)

  let open_local_file = Option.wrap open_local_file

  let url_rex = "^http(s?)://([^/]*)(.*)$" |> Re.Pcre.regexp

  let wdays = [| "Sun" ; "Mon" ; "Tue" ; "Wed" ; "Thu" ; "Fri" ; "Sat" |]
  let mons = [| "Jan" ; "Feb" ; "Mar" ; "Apr" ; "May" ; "Jun" ;
                "Jul" ; "Aug" ; "Sep" ; "Oct" ; "Nov" ; "Dec" |]

  let fetch_with_cache url =
    let cache_name = Filename.concat Xdg.cache_dir (Base64.encode_string url) in
    let ifnt =
      if not @@ Sys.file_exists cache_name then [] else
      let mtime = Unix.(gmtime (stat cache_name).st_mtime) in
      let mtime_str = Printf.sprintf "%s, %02d %s %04d %02d:%02d:%02d GMT"
          wdays.(mtime.tm_wday)
          mtime.tm_mday mons.(mtime.tm_mon) (mtime.tm_year + 1900)
          mtime.tm_hour mtime.tm_min mtime.tm_sec
      in
      ["If-Modified-Since", mtime_str]
    in
    let () = match Ezcurl.get ~headers:ifnt ~url () with
      | Ok resp when resp.code = 200 ->
          (* Output.msg_printf "Fetched: %s" url ; *)
          let ch = Stdlib.open_out_bin cache_name in
          Stdlib.output_string ch resp.body ;
          Stdlib.close_out ch
      | Ok resp when resp.code = 304 ->
          (* Output.msg_printf "Found in cache: %s" url ; *)
          ()
      | Ok resp ->
          failwithf "Unexpected HTTP %d" resp.code
      | Error (_, msg) ->
          failwithf "Unexpected libcurl error: %s" msg
    in
    cache_name

  let open_url source =
    let fields = Re.Pcre.extract ~rex:url_rex source in
    let url_secure = Array.get fields 1 in
    let url_host = Array.get fields 2 in
    let url_path =
      let p = Array.get fields 3 in
      if String.length p > 0 then
        String.sub p 1 (String.length p - 1)
      else ""
    in
    let cache_file = fetch_with_cache source in
    let module Src = struct
      let path = source
      let mtime = Unix.((stat cache_file).st_mtime)
      let dir =
        Printf.sprintf "http%s://%s/%s" url_secure url_host
          (Filename.dirname url_path)
        |> Option.some
      let lex with_positions =
        let ch = Stdlib.open_in_bin cache_file in
        let lb = Lexing.from_channel ~with_positions ch in
        lb.lex_curr_p <- { lb.lex_curr_p with pos_fname = source } ;
        lb
    end in
    (module Src : SOURCE)

  let open_url = Option.wrap open_url

  let openers = [
    open_url ;
    open_local_file ;
  ]
end

let read source =
  let rec spin ops =
    match ops with
    | [] -> failwithf "Opening: %s" source
    | op :: ops ->
        match op source with
        | Some s -> s
        | None -> (spin[@tailrec]) ops
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
      if Re.Pcre.pmatch ~rex:url_rex path
         || not @@ Filename.check_suffix path ".thm"
      then
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
          bugf "Repeated close() of sink for: %s" path ;
  end in
  (module Thm : THM)
