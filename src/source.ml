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

  let open_local_file =
    Result.wrap begin fun source ->
      let module Source = struct
        let path = source
        let mtime = Unix.((stat source).st_mtime)
        let dir = Some (Filename.dirname path)
        let lex with_positions =
          let ch = Stdlib.open_in_bin path in
          let lb = Lexing.from_channel ~with_positions ch in
          Lexing.set_filename lb source;
          lb
      end in
      (module Source : SOURCE)
    end

  let wdays = [| "Sun" ; "Mon" ; "Tue" ; "Wed" ; "Thu" ; "Fri" ; "Sat" |]
  let mons = [| "Jan" ; "Feb" ; "Mar" ; "Apr" ; "May" ; "Jun" ;
                "Jul" ; "Aug" ; "Sep" ; "Oct" ; "Nov" ; "Dec" |]

  let abella_agent =
    Printf.sprintf "Abella %s (using libcurl %s)"
      Version.version
      (Curl.version ())

  let http_strftime t =
    let tm = Unix.gmtime t in
    Printf.sprintf "%s, %02d %s %04d %02d:%02d:%02d GMT"
      wdays.(tm.tm_wday)
      tm.tm_mday mons.(tm.tm_mon) (tm.tm_year + 1900)
      tm.tm_hour tm.tm_min tm.tm_sec

  let fetch_with_cache url =
    let kind = "Source.fetch" in
    let cache_name = Filename.concat Xdg.cache_dir (Base64.encode_string url) in
    let ifnt =
      if not @@ Sys.file_exists cache_name then [] else
      let mtime = Unix.((stat cache_name).st_mtime) in
      let mtime_str = http_strftime mtime in
      Output.trace ~v:2 begin fun (module Trace) ->
        Trace.format ~kind "@[<v2>Found cache of: %s@,at: %s@,last modified: %s@]"
          url cache_name mtime_str ;
      end ;
      ["If-Modified-Since: " ^ mtime_str]
    in
    let cl = Curl.init () in
    Gc.finalise Curl.cleanup cl ;
    Curl.set_maxredirs cl 50 ;
    Curl.set_useragent cl abella_agent ;
    Curl.set_followlocation cl true ;
    Curl.set_httpheader cl ifnt ;
    Curl.set_url cl url ;
    Curl.set_httpget cl true ;
    let response_headers = Buffer.create 19 in
    let response_body = Buffer.create 19 in
    Curl.set_headerfunction cl begin fun str ->
      Buffer.add_string response_headers str ;
      String.length str
    end ;
    Curl.set_writefunction cl begin fun str ->
      Buffer.add_string response_body str ;
      String.length str
    end ;
    let rec make_attempt n =
      if n <= 0 then Result.error "Exceeded attempt count without success" else
      match Curl.perform cl ; Curl.CURLE_OK with
      | Curl.CURLE_OK -> begin
          let code = Curl.get_httpcode cl in
          Curl.cleanup cl ;
          if code = 200 then begin
            let ch = Stdlib.open_out_bin cache_name in
            Buffer.output_buffer ch response_body ;
            Stdlib.close_out ch ;
            Output.trace ~v:2 begin fun (module Trace) ->
              Trace.format ~kind "@[<v2>Cached: %s@,at: %s@,on: %s@]"
                url cache_name
                (http_strftime Unix.((stat cache_name).st_mtime)) ;
            end ;
            Result.ok cache_name
          end else if code = 304 then begin
            Output.trace ~v:2 begin fun (module Trace) ->
              Trace.printf ~kind "Cached version is newer (HTTP 304)"
            end ;
            Result.ok cache_name
          end else begin
            Result.error @@ Printf.sprintf "Unexpected HTTP %d" code
          end
        end
      | Curl.CURLE_AGAIN ->
          make_attempt @@ n - 1
      | code
      | exception Curl.CurlException (code, _, _) ->
          Curl.cleanup cl ;
          Result.error @@ Curl.strerror code
    in
    make_attempt 50

  let url_rex = "^http(s?)://([^/]*)(.*)$" |> Re.Pcre.regexp
  type url_fields = {
    secure : bool ;
    host : string ;
    path : string ;
  }

  let url_fields url =
    let open Result in
    let* strs = wrap (Re.Pcre.extract ~rex:url_rex) url in
    let secure = strs.(1) == "s" in
    let host = strs.(2) in
    let path = strs.(3) in
    let path = if String.length path > 0 then
        String.sub path 1 (String.length path - 1)
      else "" in
    return { secure ; host ; path }

  let open_url source =
    let open Result in
    let* fields = url_fields source in
    let cache_file =
      match fetch_with_cache source with
      | Result.Ok file -> file
      | Result.Error msg ->
          Output.trace ~v:2 begin fun (module Trace) ->
            let kind = "Source.open_url" in
            Trace.printf ~kind "CURL Failure: %s" msg ;
          end ;
          failwithf "Opening URL: %s" source
    in
    let* stat = wrap Unix.stat cache_file in
    let module Src = struct
      let path = source
      let mtime = stat.st_mtime
      let dir =
        Printf.sprintf "http%s://%s/%s"
          (if fields.secure then "s" else "")
          fields.host
          (Filename.dirname fields.path)
        |> Option.some
      let lex with_positions =
        let ch = Stdlib.open_in_bin cache_file in
        let lb = Lexing.from_channel ~with_positions ch in
        Lexing.set_filename lb source;
        lb
    end in
    return (module Src : SOURCE)

  let ipfs_rex = "^ipfs:(.*)$" |> Re.Pcre.regexp
  type ipfs_fields = {
    cid : string ;
  }

  let ipfs_fields url =
    let open Result in
    let* strs = wrap (Re.Pcre.extract ~rex:ipfs_rex) url in
    return { cid = strs.(1) }

  let open_ipfs source =
    let kind = "Source.open_ipfs" in
    let open Result in
    let* { cid } = ipfs_fields source in
    let cache_name = Filename.concat Xdg.cache_dir cid in
    let cmd = Printf.sprintf "ipfs get --timeout=10s --progress=false --output %s %s >/dev/null 2>&1"
        cache_name cid in
    Output.trace ~v:2 begin fun (module Trace) ->
      Trace.printf ~kind "Running: %s" cmd
    end ;
    if Sys.command cmd <> 0 then failwithf "Running ipfs" ;
    let* stat = wrap Unix.stat cache_name in
    let module Src = struct
      let path = source
      let mtime = stat.st_mtime
      let dir = None
      let lex with_positions =
        let ch = Stdlib.open_in_bin cache_name in
        let lb = Lexing.from_channel ~with_positions ch in
        Lexing.set_filename lb source;
        lb
    end in
    return (module Src : SOURCE)

  let openers = [
    "url", open_url ;
    "ipfs", open_ipfs ;
    "local", open_local_file ;
  ]
end

let read source =
  let rec spin ops =
    let kind = "Source.read.spin" in
    match ops with
    | [] ->
        Output.trace ~v:5 begin fun (module Trace) ->
          Trace.printf ~kind "No more openers"
        end ;
        failwithf "Opening: %s" source
    | (op_name, op_fn) :: ops ->
        match op_fn source with
        | Ok s -> s
        | Error exn ->
            Output.trace ~v:5 begin fun (module Trace) ->
              Trace.printf ~kind "%s: %s" op_name (Printexc.to_string exn)
            end ;
            (spin[@tailrec]) ops
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
