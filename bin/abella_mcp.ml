(*
 * Copyright (C) 2026  Inria
 * See LICENSE for licensing details.
 *)

(** Stdio MCP (Model Context Protocol) server for Abella with
    prefix-undo incremental checking and speculative tactic probing. *)

open Abella_lib
open Extensions

module J = Yojson.Safe

(* Incremental session cache *)

type cache = {
  mutable initialized : bool ;
  mutable path : string ;
  mutable strict : bool ;
  mutable name_mode : Session.name_mode ;
  mutable executed : Session.command_chunk list ;
}

let cache : cache = {
  initialized = false ;
  path = "" ;
  strict = false ;
  name_mode = `relaxed ;
  executed = [] ;
}

let reset_cache () =
  cache.initialized <- false ;
  cache.path <- "" ;
  cache.strict <- false ;
  cache.name_mode <- `relaxed ;
  cache.executed <- []

let read_file path =
  let ch = Stdlib.open_in_bin path in
  Fun.protect
    ~finally:(fun () -> Stdlib.close_in ch)
    (fun () ->
      let len = in_channel_length ch in
      really_input_string ch len)

let is_undo_or_reset (c : Session.command_chunk) =
  let s = String.trim c.text in
  s = "#back" || s = "#reset" || s = "undo."

let common_prefix_len (a : Session.command_chunk list) (b : Session.command_chunk list) =
  let rec loop n xs ys =
    match xs, ys with
    | x :: xs', y :: ys'
      when x.Session.text = y.Session.text
           && x.Session.start = y.Session.start
           && not (is_undo_or_reset x) ->
        loop (n + 1) xs' ys'
    | _ -> n
  in
  loop 0 a b

let take n lst =
  let rec loop acc k = function
    | _ when k <= 0 -> List.rev acc
    | [] -> List.rev acc
    | x :: xs -> loop (x :: acc) (k - 1) xs
  in
  loop [] n lst

let extract_error_message (msgs : Json.t list) =
  let errs =
    List.filter_map
      (function
        | `Assoc fields -> begin
            match List.assoc_opt "type" fields,
                  List.assoc_opt "severity" fields,
                  List.assoc_opt "message" fields with
            | Some (`String "system_message"),
              Some (`String "error"),
              Some (`String m) -> Some m
            | _ -> None
          end
        | _ -> None)
      msgs
  in
  match errs with
  | [] -> "Command failed"
  | _ -> String.concat "\n" errs

let extract_messages_text (msgs : Json.t list) =
  List.filter_map
    (function
      | `Assoc fields -> begin
          match List.assoc_opt "type" fields,
                List.assoc_opt "message" fields with
          | Some (`String "system_message"), Some (`String m) -> Some m
          | _ -> None
        end
      | _ -> None)
    msgs

let sync_to ~path ~contents ~strict ~name_mode ?until_line () =
  let all_cmds = Session.split_commands ~filename:path contents in
  let target_cmds =
    match until_line with
    | None -> all_cmds
    | Some line ->
        let rec prefix acc = function
          | [] -> List.rev acc
          | (c : Session.command_chunk) :: rest ->
              if c.start.line > line then List.rev acc
              else prefix (c :: acc) rest
        in
        prefix [] all_cmds
  in
  let need_reinit =
    not cache.initialized
    || cache.path <> path
    || cache.strict <> strict
    || cache.name_mode <> name_mode
  in
  let init_res =
    if need_reinit then begin
      let out =
        Session.init ~root:path ~strict ~name_mode
          ~trust_compiled:false ~welcome:false ()
      in
      if not out.ok then
        Error (`Init_error (extract_error_message out.messages))
      else begin
        cache.initialized <- true ;
        cache.path <- path ;
        cache.strict <- strict ;
        cache.name_mode <- name_mode ;
        cache.executed <- [] ;
        Ok ()
      end
    end else Ok ()
  in
  match init_res with
  | Error _ as e -> e
  | Ok () ->
      let common = common_prefix_len cache.executed target_cmds in
      let to_undo = List.length cache.executed - common in
      let undo_ok =
        if to_undo > 0 then begin
          let out = Session.back to_undo in
          if out.ok then begin
            cache.executed <- take common cache.executed ;
            true
          end else begin
            (* Fallback to clean reinit if undo stack cannot go back *)
            let init_out =
              Session.init ~root:path ~strict ~name_mode
                ~trust_compiled:false ~welcome:false ()
            in
            cache.executed <- [] ;
            init_out.ok
          end
        end else true
      in
      if not undo_ok then
        Error (`Init_error "Failed to reinitialize session")
      else begin
        let rec drop k lst =
          if k <= 0 then lst
          else match lst with [] -> [] | _ :: xs -> drop (k - 1) xs
        in
        let reused = List.length cache.executed in
        let to_run = drop reused target_cmds in
        let rec run_all = function
          | [] -> Ok (List.length target_cmds, reused)
          | (c : Session.command_chunk) :: rest ->
              let out = Session.process ~start:c.start c.text in
              if out.ok then begin
                cache.executed <- cache.executed @ [c] ;
                run_all rest
              end else
                Error (`Cmd_error (c, out, reused))
        in
        run_all to_run
      end

(* JSON argument helpers *)

let get_string args key =
  match args with
  | `Assoc fields -> begin
      match List.assoc_opt key fields with
      | Some (`String s) -> Some s
      | _ -> None
    end
  | _ -> None

let get_int args key =
  match args with
  | `Assoc fields -> begin
      match List.assoc_opt key fields with
      | Some (`Int n) -> Some n
      | _ -> None
    end
  | _ -> None

let get_bool args key ~default =
  match args with
  | `Assoc fields -> begin
      match List.assoc_opt key fields with
      | Some (`Bool b) -> b
      | _ -> default
    end
  | _ -> default

let name_mode_of_opt = function
  | Some "warn" -> `warn
  | Some "strict" -> `strict
  | _ -> `relaxed

let state_json_or_null () =
  match Session.current_state () with
  | Some s -> s
  | None -> `Null

let load_contents args path =
  match get_string args "contents" with
  | Some c -> Ok c
  | None ->
      try Ok (read_file path)
      with Sys_error msg -> Error msg

let sync_from_args args ?until_line () =
  match get_string args "path" with
  | None -> Error (`Arg_error "Missing required string parameter: path")
  | Some path ->
      match load_contents args path with
      | Error msg -> Error (`Arg_error ("Cannot read file: " ^ msg))
      | Ok contents ->
          let strict = get_bool args "strict" ~default:false in
          let name_mode = name_mode_of_opt (get_string args "name_mode") in
          match sync_to ~path ~contents ~strict ~name_mode ?until_line () with
          | Ok res -> Ok res
          | Error (`Init_error msg) -> Error (`Arg_error msg)
          | Error (`Cmd_error (c, out, reused)) ->
              Error (`Exec_error (c, out, reused))

let sync_error_json = function
  | `Arg_error msg ->
      `Assoc [
        "ok", `Bool false ;
        "error", `Assoc [ "message", `String msg ] ;
      ]
  | `Exec_error (c, out, reused) ->
      let msg = extract_error_message out.Session.messages in
      `Assoc [
        "ok", `Bool false ;
        "reused_prefix", `Int reused ;
        "error", `Assoc [
          "line", `Int c.Session.start.line ;
          "col", `Int (c.Session.start.offset - c.Session.start.bol + 1) ;
          "command", `String (String.trim c.text) ;
          "message", `String msg ;
          "in_proof", `Bool (Session.in_proof ()) ;
          "state", state_json_or_null () ;
          "display", `String (Session.current_display ()) ;
        ] ;
      ]

(* Tool implementations *)

let tool_check_file args =
  match sync_from_args args () with
  | Error e -> sync_error_json e
  | Ok (checked, reused) ->
      `Assoc [
        "ok", `Bool true ;
        "commands_checked", `Int checked ;
        "reused_prefix", `Int reused ;
        "in_proof", `Bool (Session.in_proof ()) ;
        "state", state_json_or_null () ;
        "display", `String (Session.current_display ()) ;
      ]

let tool_get_state args =
  match get_int args "line" with
  | None ->
      `Assoc [
        "ok", `Bool false ;
        "error", `Assoc [ "message", `String "Missing required integer parameter: line" ] ;
      ]
  | Some line ->
      match sync_from_args args ~until_line:line () with
      | Error e -> sync_error_json e
      | Ok (checked, reused) ->
          `Assoc [
            "ok", `Bool true ;
            "line", `Int line ;
            "commands_checked", `Int checked ;
            "reused_prefix", `Int reused ;
            "in_proof", `Bool (Session.in_proof ()) ;
            "state", state_json_or_null () ;
            "display", `String (Session.current_display ()) ;
          ]

let normalize_tactic_text s =
  let s = String.trim s in
  if s = "" then s
  else
    let is_bullet =
      String.for_all (fun c -> c = '-' || c = '+' || c = '*') s
    in
    if is_bullet || s.[String.length s - 1] = '.' then s
    else s ^ "."

let tool_try_tactic args =
  match get_int args "line", get_string args "tactic" with
  | None, _ ->
      `Assoc [
        "ok", `Bool false ;
        "error", `Assoc [ "message", `String "Missing required integer parameter: line" ] ;
      ]
  | _, None ->
      `Assoc [
        "ok", `Bool false ;
        "error", `Assoc [ "message", `String "Missing required string parameter: tactic" ] ;
      ]
  | Some line, Some raw_tactic ->
      match sync_from_args args ~until_line:line () with
      | Error e -> sync_error_json e
      | Ok (_checked, reused) ->
          let tactic = normalize_tactic_text raw_tactic in
          let out = Session.try_command tactic in
          let msgs_text = extract_messages_text out.messages in
          let completed =
            List.exists (fun m -> String.starts_with ~prefix:"Proof completed" m) msgs_text
          in
          let result_state =
            let end_states =
              List.filter_map
                (function
                  | `Assoc fields -> begin
                      match List.assoc_opt "type" fields,
                            List.assoc_opt "end_state" fields with
                      | Some (`String "proof_command"), Some st -> Some st
                      | _ -> None
                    end
                  | _ -> None)
                out.messages
            in
            match List.rev end_states with
            | st :: _ -> st
            | [] -> `Null
          in
          if out.ok then
            `Assoc [
              "ok", `Bool true ;
              "tactic", `String tactic ;
              "reused_prefix", `Int reused ;
              "completed_proof", `Bool completed ;
              "state", result_state ;
              "messages", `List (List.map (fun s -> `String s) msgs_text) ;
            ]
          else
            `Assoc [
              "ok", `Bool false ;
              "tactic", `String tactic ;
              "reused_prefix", `Int reused ;
              "error", `String (extract_error_message out.messages) ;
              "messages", `List (List.map (fun s -> `String s) msgs_text) ;
            ]

let contains_ci ~needle haystack =
  let n = String.lowercase_ascii needle in
  let h = String.lowercase_ascii haystack in
  let nl = String.length n and hl = String.length h in
  if nl = 0 then true
  else
    let rec spin i =
      i + nl <= hl && (String.sub h i nl = n || spin (i + 1))
    in
    spin 0

let tool_search_lemmas args =
  let query = Option.value (get_string args "query") ~default:"" in
  let limit = Option.value (get_int args "limit") ~default:20 in
  let until_line = get_int args "line" in
  match sync_from_args args ?until_line () with
  | Error e -> sync_error_json e
  | Ok _ ->
      let matches = ref [] in
      Hashtbl.iter
        (fun name (tys, thm) ->
          let stmt =
            Format.asprintf "%t" (Prover.print_theorem name (tys, thm))
            |> String.trim
          in
          if contains_ci ~needle:query name || contains_ci ~needle:query stmt then
            matches := (name, stmt) :: !matches)
        Prover.lemmas ;
      let sorted =
        List.sort (fun (a, _) (b, _) -> String.compare a b) !matches
      in
      let total = List.length sorted in
      let limited = take (max 0 limit) sorted in
      `Assoc [
        "ok", `Bool true ;
        "total_matches", `Int total ;
        "matches", `List (List.map (fun (name, stmt) ->
            `Assoc [
              "name", `String name ;
              "statement", `String stmt ;
            ]) limited) ;
      ]

let format_def (def : Types.def) =
  let kw = match def.flavor with
    | Types.Inductive -> "Define"
    | Types.CoInductive -> "CoDefine"
  in
  let preds =
    Term.Itab.bindings def.mutual
    |> List.map (fun (id, ty) -> id ^ " : " ^ Term.ty_to_string ty)
    |> String.concat ", "
  in
  let cls =
    List.map
      (fun (c : Types.def_clause) ->
        if c.body = Metaterm.True then
          Metaterm.metaterm_to_formatted_string c.head
        else
          Printf.sprintf "%s := %s"
            (Metaterm.metaterm_to_formatted_string c.head)
            (Metaterm.metaterm_to_formatted_string c.body))
      def.clauses
    |> String.concat ";\n"
  in
  Printf.sprintf "%s %s by\n%s." kw preds cls

let tool_show args =
  match get_string args "name" with
  | None ->
      `Assoc [
        "ok", `Bool false ;
        "error", `Assoc [ "message", `String "Missing required string parameter: name" ] ;
      ]
  | Some name ->
      let until_line = get_int args "line" in
      match sync_from_args args ?until_line () with
      | Error e -> sync_error_json e
      | Ok _ ->
          try
            let text = Format.asprintf "%t" (Prover.show name) |> String.trim in
            `Assoc [
              "ok", `Bool true ;
              "name", `String name ;
              "kind", `String "theorem_or_sealed" ;
              "definition", `String text ;
            ]
          with _ ->
            begin match Hashtbl.find_opt Prover.defs_table name with
            | Some def ->
                `Assoc [
                  "ok", `Bool true ;
                  "name", `String name ;
                  "kind", `String "definition" ;
                  "definition", `String (format_def def) ;
                ]
            | None ->
                `Assoc [
                  "ok", `Bool false ;
                  "error", `Assoc [
                    "message", `String (Printf.sprintf "Unknown theorem, sealed type, or definition: %s" name) ;
                  ] ;
                ]
            end

let tool_reset _args =
  reset_cache () ;
  `Assoc [ "ok", `Bool true ]

(* MCP tool schema registry *)

let prop_path =
  "path", `Assoc [
    "type", `String "string" ;
    "description", `String "Path to the .thm or .thmod file." ;
  ]

let prop_contents =
  "contents", `Assoc [
    "type", `String "string" ;
    "description", `String "Optional unsaved file contents; if omitted, reads from disk." ;
  ]

let prop_line =
  "line", `Assoc [
    "type", `String "integer" ;
    "description", `String "1-based line number in the file." ;
  ]

let prop_strict =
  "strict", `Assoc [
    "type", `String "boolean" ;
    "description", `String "Treat stratification warnings as errors." ;
  ]

let prop_name_mode =
  "name_mode", `Assoc [
    "type", `String "string" ;
    "enum", `List [`String "relaxed" ; `String "warn" ; `String "strict"] ;
    "description", `String "Handling of system-generated names." ;
  ]

let tool_schema ~name ~description ~properties ~required =
  `Assoc [
    "name", `String name ;
    "description", `String description ;
    "inputSchema", `Assoc [
      "type", `String "object" ;
      "properties", `Assoc properties ;
      "required", `List (List.map (fun s -> `String s) required) ;
    ] ;
  ]

let tools_list_json : Json.t =
  `Assoc [
    "tools", `List [
      tool_schema
        ~name:"check_file"
        ~description:"Incrementally check an Abella .thm/.thmod file using prefix-undo caching."
        ~properties:[prop_path ; prop_contents ; prop_strict ; prop_name_mode]
        ~required:["path"] ;
      tool_schema
        ~name:"get_state"
        ~description:"Get the Abella proof state (hypotheses, variables, goals) at a given line."
        ~properties:[prop_path ; prop_line ; prop_contents ; prop_strict ; prop_name_mode]
        ~required:["path" ; "line"] ;
      tool_schema
        ~name:"try_tactic"
        ~description:"Speculatively run a tactic at a given line without modifying the file or cached state."
        ~properties:[
          prop_path ;
          prop_line ;
          ("tactic", `Assoc [
             "type", `String "string" ;
             "description", `String "Abella tactic or bullet to test (trailing '.' added if omitted)." ;
           ]) ;
          prop_contents ;
          prop_strict ;
          prop_name_mode ;
        ]
        ~required:["path" ; "line" ; "tactic"] ;
      tool_schema
        ~name:"search_lemmas"
        ~description:"Search lemmas in scope by substring against name or statement."
        ~properties:[
          prop_path ;
          ("query", `Assoc [
             "type", `String "string" ;
             "description", `String "Case-insensitive substring to match (empty string lists all)." ;
           ]) ;
          prop_line ;
          ("limit", `Assoc [
             "type", `String "integer" ;
             "description", `String "Maximum number of matches to return (default 20)." ;
           ]) ;
          prop_contents ;
        ]
        ~required:["path" ; "query"] ;
      tool_schema
        ~name:"show"
        ~description:"Show the statement or clauses of a theorem, sealed type, or inductive definition in scope."
        ~properties:[
          prop_path ;
          ("name", `Assoc [
             "type", `String "string" ;
             "description", `String "Name of the theorem, sealed type, or defined predicate." ;
           ]) ;
          prop_line ;
          prop_contents ;
        ]
        ~required:["path" ; "name"] ;
      tool_schema
        ~name:"reset"
        ~description:"Clear the incremental session cache."
        ~properties:[]
        ~required:[] ;
    ]
  ]

(* JSON-RPC 2.0 stdio transport *)

let rpc_result id result =
  `Assoc [
    "jsonrpc", `String "2.0" ;
    "id", id ;
    "result", result ;
  ]

let rpc_error id code message =
  `Assoc [
    "jsonrpc", `String "2.0" ;
    "id", id ;
    "error", `Assoc [
      "code", `Int code ;
      "message", `String message ;
    ] ;
  ]

let call_tool name args =
  let json =
    match name with
    | "check_file" -> tool_check_file args
    | "get_state" -> tool_get_state args
    | "try_tactic" -> tool_try_tactic args
    | "search_lemmas" -> tool_search_lemmas args
    | "show" -> tool_show args
    | "reset" -> tool_reset args
    | _ ->
        `Assoc [
          "ok", `Bool false ;
          "error", `Assoc [ "message", `String ("Unknown tool: " ^ name) ] ;
        ]
  in
  let is_error =
    match json with
    | `Assoc fields -> List.assoc_opt "ok" fields = Some (`Bool false)
    | _ -> false
  in
  `Assoc [
    "content", `List [
      `Assoc [
        "type", `String "text" ;
        "text", `String (J.to_string json) ;
      ]
    ] ;
    "isError", `Bool is_error ;
  ]

let handle_request line =
  let msg =
    try Ok (J.from_string line)
    with Yojson.Json_error e -> Error e
  in
  match msg with
  | Error e ->
      Some (rpc_error `Null (-32700) ("Parse error: " ^ e))
  | Ok (`Assoc fields) -> begin
      let id_opt = List.assoc_opt "id" fields in
      let method_name =
        match List.assoc_opt "method" fields with
        | Some (`String m) -> Some m
        | _ -> None
      in
      let params =
        match List.assoc_opt "params" fields with
        | Some p -> p
        | None -> `Assoc []
      in
      match method_name, id_opt with
      | None, _ ->
          Option.map (fun id -> rpc_error id (-32600) "Invalid Request") id_opt
      | Some m, None when String.starts_with ~prefix:"notifications/" m ->
          None
      | Some m, None ->
          let _ = m in None
      | Some "initialize", Some id ->
          Some (rpc_result id (`Assoc [
              "protocolVersion", `String "2024-11-05" ;
              "capabilities", `Assoc [
                "tools", `Assoc [] ;
              ] ;
              "serverInfo", `Assoc [
                "name", `String "abella_mcp" ;
                "version", `String Version.version ;
              ] ;
            ]))
      | Some "ping", Some id ->
          Some (rpc_result id (`Assoc []))
      | Some "tools/list", Some id ->
          Some (rpc_result id tools_list_json)
      | Some "tools/call", Some id -> begin
          match get_string params "name" with
          | None ->
              Some (rpc_error id (-32602) "Missing tool name")
          | Some name ->
              let args =
                match params with
                | `Assoc pf ->
                    Option.value (List.assoc_opt "arguments" pf) ~default:(`Assoc [])
                | _ -> `Assoc []
              in
              Some (rpc_result id (call_tool name args))
        end
      | Some m, Some id ->
          Some (rpc_error id (-32601) ("Method not found: " ^ m))
    end
  | Ok _ ->
      Some (rpc_error `Null (-32600) "Invalid Request")

let run_server () =
  let rec loop () =
    match input_line stdin with
    | line ->
        let trimmed = String.trim line in
        if trimmed <> "" then begin
          match handle_request trimmed with
          | None -> ()
          | Some resp ->
              output_string stdout (J.to_string resp) ;
              output_char stdout '\n' ;
              flush stdout
        end ;
        loop ()
    | exception End_of_file -> 0
  in
  loop ()

let () =
  let open Cmdliner in
  let doc = "Run the Abella stdio MCP server." in
  let info = Cmd.info "abella_mcp" ~doc ~version:Version.version in
  let cmd = Cmd.v info Term.(const run_server $ const ()) in
  Stdlib.exit (Cmd.eval' cmd)
