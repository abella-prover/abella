(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Generate documentation for a collection of Abella .thm files *)

open Extensions

module Dist = Abella_doc_dist
let css_content = Dist.read "abella_doc.css" |> Option.get
let js_content = Dist.read "abella_doc.js" |> Option.get

(******************************************************************************)

let html_escape str =
  let buf = Buffer.create (String.length str) in
  String.iter begin function
  | '<' -> Buffer.add_string buf "&lt;"
  | '>' -> Buffer.add_string buf "&gt;"
  | '&' -> Buffer.add_string buf "&amp;"
  | c -> Buffer.add_char buf c
  end str ;
  Buffer.contents buf

let file_contents fn =
  let ch = open_in_bin fn in
  let str = really_input_string ch (in_channel_length ch) in
  close_in ch ;
  str

let thm_template base =
  let root = Filename.basename base in
  let thm_contents = file_contents (base ^ ".thm") in
  let thm_json = Json.from_file (base ^ ".json") in
  {|<!DOCTYPE html>
<html lang="en"><head>
  <meta charset="UTF-8">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>|} ^ root ^ {|.thm [Abella trace]</title>
  <link rel="stylesheet" href="https://fonts.googleapis.com/icon?family=Material+Icons">
  <style>|} ^ css_content ^ {|</style>
</head><body>
  <div id="logobox">
    <a href="https://abella-prover.org/index.html"><img src="https://abella-prover.org/images/logo-small.png" alt="Abella logo (small)"></a>
    <h1 id="thmname">|} ^ root ^ {|.thm</h1>
  </div>
  <div id="outer-container">
    <div id="container">
      <div id="thmbox"><div class="default-contents">|} ^ html_escape thm_contents ^ {|</div></div>
    </div>
  </div>
  <script type="module">
|} ^ js_content ^ {|
    const thmContent = |} ^ Json.to_string (`String thm_contents) ^ {|;
    const thmJson = |} ^ Json.to_string thm_json ^ {|;
    await loadModule("thmbox", thmContent, thmJson);
  </script>
</body></html>|} ;;

let lp_template root =
  let base = Filename.basename root in
  let sig_contents = file_contents (root ^ ".sig") in
  let sig_json = Json.from_file (root ^ ".sig.json") in
  let mod_contents = file_contents (root ^ ".mod") in
  let mod_json = Json.from_file (root ^ ".mod.json") in
  {|<!DOCTYPE html>
<html lang="en"><head>
  <meta charset="UTF-8">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>|} ^ base ^ {| [&lambda;Prolog]</title>
  <style>|} ^ css_content ^ {|</style>
</head><body>
  <div id="logobox">
    <a href="https://abella-prover.org/index.html"><img src="https://abella-prover.org/images/logo-small.png"></a>
    <h1 id="thmname">&lambda;Prolog module <strong>|} ^ base ^ {|</strong></h1>
  </div>
  <div class="outer-container">
    <h2><strong><tt>|} ^ base ^ {|.sig</tt></strong></h2>
    <div class="container">
      <div id="sigbox"><div class="default-contents">|} ^ html_escape sig_contents ^ {|</div></div>
    </div>
  </div>
  <div class="outer-container">
    <h2><strong><tt>|} ^ base ^ {|.mod</tt></strong></h2>
    <div class="container">
      <div id="modbox"><div class="default-contents">|} ^ html_escape mod_contents ^ {|</div></div>
    </div>
  </div>
  <script type="module">
|} ^ js_content ^ {|
    const sigContents = |} ^ Json.to_string (`String sig_contents) ^ {|;
    const sigJson = |} ^ Json.to_string sig_json ^ {|;
    const modContents = |} ^ Json.to_string (`String mod_contents) ^ {|;
    const modJson = |} ^ Json.to_string mod_json ^ {|;
    await loadLP("sigbox", sigContents, sigJson,
                 "modbox", modContents, modJson);
  </script>
</body></html>|} ;;

(******************************************************************************)

open Extensions

type conf = {
  abella : string ;
  recursive : bool ;
  verbose : bool ;
}

let mk_conf abella recursive verbose =
  { abella ; recursive ; verbose }

let vprintf conf =
  if conf.verbose
  then (fun fmt -> Printf.printf (fmt ^^ "\n%!"))
  else Printf.ifprintf stdout

let json_of_position (lft, rgt) =
  let open Lexing in
  if ( lft = Lexing.dummy_pos
       || lft.pos_fname = ""
       || lft.pos_fname <> rgt.pos_fname )
  then `Null else
    `List [
      `Int lft.pos_cnum ;
      `Int rgt.pos_cnum ;
    ]

let dep_tab = Hashtbl.create 19

let ignore_list = [ "node_modules" ; "build" ; "dist" ; "css" ; "js" ]

let rec process conf file =
  let file_bn = Filename.basename file in
  if List.mem file_bn ignore_list then () else
  let open Unix in
  let stats = stat file in
  match stats.st_kind with
  | S_DIR when conf.recursive ->
      process_directory conf file
  | S_REG ->
      if Hashtbl.mem dep_tab file then () else begin
        Hashtbl.replace dep_tab file [] ;
        if Filename.check_suffix file ".sig" then
          process_sig conf file
        else if Filename.check_suffix file ".mod" then begin
          let base = Filename.chop_suffix file ".mod" in
          if not @@ Sys.file_exists (base ^ ".sig") then
            failwithf "Cannot find %s.sig" base
        end else if Filename.check_suffix file ".thm" then
          process_thm conf file
        else
          vprintf conf "IGNORE: %s" file
      end
  | _ ->
      (* ignore all other files *)
      vprintf conf "IGNORE: %s" file

and process_sig conf file =
  if not @@ Filename.is_relative file then
    failwithf "cannot handle absolute paths: %s" file ;
  let base = Filename.chop_suffix file ".sig" in
  let Sig lpsig = Accumulate.read_lpsig base in
  let annots = ref [] in
  let emit annot = annots := annot :: !annots in
  emit @@ `Assoc [ "kind", `String "name" ;
                   "range", json_of_position lpsig.name.pos ] ;
  List.iter begin fun (acc : _ wpos) ->
    emit @@ `Assoc [ "kind", `String "accum_sig" ;
                     "range", json_of_position acc.pos ]
  end lpsig.accum_sig ;
  List.iter begin fun (decl : _ wpos) ->
    emit @@ `Assoc [ "kind", `String "decl" ;
                     "range", json_of_position decl.pos ]
  end lpsig.decls ;
  let json = `List (List.rev !annots) in
  let out = open_out_bin (file ^ ".json") in
  output_string out (Json.to_string json) ;
  close_out out ;
  vprintf conf "LPSIG: %s -> %s.json" file file ;
  process_mod conf (base ^ ".mod")

and process_mod conf file =
  let base = Filename.chop_suffix file ".mod" in
  let Mod lpmod = Accumulate.read_lpmod base in
  let annots =
    `Assoc [ "kind", `String "name" ;
             "range", json_of_position lpmod.name.pos ] ::
    List.map begin fun (acc : _ wpos) ->
      `Assoc [ "kind", `String "accum" ;
               "range", json_of_position acc.pos ]
    end lpmod.accum @
    List.map begin fun (cl : _ wpos) ->
      `Assoc [ "kind", `String "clause" ;
               "range", json_of_position cl.pos ]
    end lpmod.clauses in
  let json = `List annots in
  let out = open_out_bin (file ^ ".json") in
  output_string out (Json.to_string json) ;
  close_out out ;
  vprintf conf "LPMOD: %s -> %s.json" file file ;
  let html_file = base ^ ".lp.html" in
  let out = open_out_bin html_file in
  output_string out (lp_template base) ;
  close_out out ;
  vprintf conf "CREATE: %s" html_file

and process_thm conf file =
  let base = Filename.chop_suffix file ".thm" in
  let (specs, deps) = Depend.thm_dependencies base in
  let deps = specs @ List.rev_map (fun f -> f ^ ".thm") deps in
  Hashtbl.replace dep_tab file deps ;
  List.iter (process conf) deps

and process_directory conf dir =
  let fs = Sys.readdir dir in
  Array.fast_sort String.compare fs ;
  Array.iter (fun file -> process conf (Filename.concat dir file)) fs

let main conf files =
  (* Arg.parse options add_input_file usage_message ; *)
  List.iter (process conf) files ;
  let seen = Hashtbl.create (Hashtbl.length dep_tab) in
  let topo = ref [] in
  let rec toproc file =
    if Hashtbl.mem seen file then () else begin
      Hashtbl.replace seen file () ;
      List.iter toproc (Hashtbl.find dep_tab file) ;
      topo := file :: !topo ;
    end in
  Hashtbl.iter (fun f _ -> toproc f) dep_tab ;
  List.iter begin fun file ->
    if not @@ Filename.check_suffix file ".thm" then () else
    let root = Filename.chop_suffix file ".thm" in
    let cmd = Printf.sprintf "%s --non-recursive --annotate --output=%s.json %s.thm"
        conf.abella root root in
    vprintf conf "RUN: %s" cmd ;
    if Sys.command cmd != 0 then
      failwithf "ERROR running: %s" cmd ;
    let htmlfile = root ^ ".html" in
    let ch = open_out_bin htmlfile in
    output_string ch (thm_template root) ;
    close_out ch ;
    vprintf conf "CREATE: %s" htmlfile
  end (List.rev !topo)

(******************************************************************************)
(* Command line parsing *)

let () =
  let open Cmdliner in
  let conf =
    let abella =
      let default =
        let dir = Filename.dirname Sys.executable_name in
        let ab1 = Filename.concat dir "abella" in
        let ab2 = Filename.concat dir "abella.exe" in
        if Sys.file_exists ab1 then ab1 else ab2 in
      let env = Cmd.Env.info "ABELLA"
          ~doc:"Abella command to run (overriden by $(b,--abella))" in
      let doc = "Set the Abella command to $(docv)" in
      Arg.(value @@ opt string default @@
           info ["a" ; "abella"] ~doc ~env
             ~docv:"CMD"
             ~absent:"$(b,abella[.exe])")
    in
    let verbose =
      let doc = "Verbose output" in
      Arg.(value @@ flag @@ info ["verbose"] ~doc)
    in
    let recursive =
      let doc = "Process directories recursively" in
      Arg.(value @@ flag @@ info ["r"] ~doc)
    in
    Term.(const mk_conf $ abella $ recursive $ verbose)
  in
  let files =
    let doc = "An Abella $(b,.thm) file or a directory" in
    Arg.(value @@ pos_all string [] @@ info [] ~docv:"SOURCE" ~doc)
  in
  let cmd =
    let doc = "Generate HTML documentation from Abella source" in
    let man = [
      `S Manpage.s_examples ;
      `Blocks [
        `P "To create HTML documents from a.thm, d/b.thm, and c/*.thm" ;
        `Pre "  \\$ $(tname) a.thm d/b.thm c/*.thm" ;
        `P "To create HTML documentation recursively from all .thm files in d/" ;
        `Pre "  \\$ $(tname) -r d" ;
      ] ;
      `S Manpage.s_bugs ;
      `P "File bug reports on <$(b,https://github.com/abella-prover/abella/issues)>" ;
    ] in
    let info = Cmd.info "abella_doc" ~doc ~man ~exits:[] in
    Cmd.v info @@ Term.(const main $ conf $ files)
  in
  exit (Cmd.eval cmd)
