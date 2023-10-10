(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Generate documentation for a collection of Abella .thm files *)

module Dist = Abella_doc_dist
let css_content = Dist.read "abella_doc.css" |> Option.get
let js_content = Dist.read "abella_doc.js" |> Option.get

(******************************************************************************)

let safe_file_contents fn =
  let ch = open_in_bin fn in
  let str = really_input_string ch (in_channel_length ch) in
  close_in ch ;
  let buf = Buffer.create (String.length str) in
  String.iter begin function
  | '<' -> Buffer.add_string buf "&lt;"
  | '>' -> Buffer.add_string buf "&gt;"
  | '&' -> Buffer.add_string buf "&amp;"
  | c -> Buffer.add_char buf c
  end str ;
  Buffer.contents buf

let thm_template base =
  let root = Filename.basename base in
  let thmfile = root ^ ".thm" in
  let jsonfile = root ^ ".json" in
  let thmfile_contents = safe_file_contents (base ^ ".thm") in
  {|<!DOCTYPE html>
<html lang="en"><head>
  <meta charset="UTF-8">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>|} ^ base ^ {|.thm [Abella trace]</title>
  <link rel="stylesheet" href="https://fonts.googleapis.com/icon?family=Material+Icons">
  <style>|} ^ css_content ^ {|</style>
</head><body>
  <div id="logobox">
    <a href="https://abella-prover.org/index.html"><img src="https://abella-prover.org/images/logo-small.png"></a>
    <h1 id="thmname">|} ^ root ^ {|.thm</h1>
  </div>
  <div id="outer-container">
    <div id="container">
      <div id="thmbox"><div class="default-contents">|} ^ thmfile_contents ^ {|</div></div>
    </div>
  </div>
  <script type="module">
|} ^ js_content ^ {|
await loadModule("thmbox", "|} ^ thmfile ^ {|", "|} ^ jsonfile ^ {|");
  </script>
</body></html>|} ;;

let lp_template root =
  let base = Filename.basename root in
  let sig_src = base ^ ".sig" in
  let sig_contents = safe_file_contents (root ^ ".sig") in
  let sig_json = base ^ ".sig.json" in
  let mod_src = base ^ ".mod" in
  let mod_contents = safe_file_contents (root ^ ".mod") in
  let mod_json = base ^ ".mod.json" in
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
      <div id="sigbox"><div class="default-contents">|} ^ sig_contents ^ {|</div></div>
    </div>
  </div>
  <div class="outer-container">
    <h2><strong><tt>|} ^ base ^ {|.mod</tt></strong></h2>
    <div class="container">
      <div id="modbox"><div class="default-contents">|} ^ mod_contents ^ {|</div></div>
    </div>
  </div>
  <script type="module">
|} ^ js_content ^ {|
await loadLP("sigbox", "|} ^ sig_src ^ {|", "|} ^ sig_json ^ {|",
             "modbox", "|} ^ mod_src ^ {|", "|} ^ mod_json ^ {|");
  </script>
</body></html>|} ;;

(******************************************************************************)

open Extensions

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

let abella =
  let dir = Filename.dirname Sys.executable_name in
  let ab1 = Filename.concat dir "abella" in
  let ab2 = Filename.concat dir "abella.exe" in
  ref @@ if Sys.file_exists ab1 then ab1 else ab2

let recursive = ref false

let options = Arg.[
    "-a", Set_string abella,
    Printf.sprintf "PROG Run PROG as abella (default: %s)" !abella ;
    "-r", Arg.Set recursive, " Recursively process directories" ;
  ] |> Arg.align

let input_files : string list ref = ref []

let add_input_file file =
  input_files := file :: !input_files

let usage_message = Printf.sprintf "Usage: %s [options] [<theorem-file> | <directory>] ..." begin
    if !Sys.interactive then "abella_doc" else Sys.argv.(0) (*Filename.basename Sys.executable_name*)
  end

let dep_tab = Hashtbl.create (List.length !input_files)

let ignore_list = [ "node_modules" ; "build" ; "dist" ; "css" ; "js" ]

let rec process file =
  let file_bn = Filename.basename file in
  if List.mem file_bn ignore_list then () else
  let open Unix in
  let stats = stat file in
  match stats.st_kind with
  | S_DIR when !recursive ->
      process_directory file
  | S_REG ->
      if Hashtbl.mem dep_tab file then () else begin
        Hashtbl.replace dep_tab file [] ;
        if Filename.check_suffix file ".sig" then
          process_sig file
        else if Filename.check_suffix file ".mod" then
          process_mod file
        else if Filename.check_suffix file ".thm" then
          process_thm file
        (* else *)
        (*   Printf.printf "IGNORE: %s\n%!" file *)
      end
  | _ ->
      (* ignore all other files *)
      Printf.printf "IGNORE: %s\n%!" file

and process_sig file =
  if not @@ Filename.is_relative file then
    failwithf "cannot handle absolute paths: %s" file ;
  let base = Filename.chop_suffix file ".sig" in
  let Sig lpsig = Accumulate.read_lpsig base in
  let annots = ref [] in
  let emit annot = annots := annot :: !annots in
  emit @@ `Assoc [ "kind", `String "name" ;
                   "range", json_of_position lpsig.name.pos ] ;
  List.iter begin fun (acc : _ Typing.wpos) ->
    emit @@ `Assoc [ "kind", `String "accum_sig" ;
                     "range", json_of_position acc.pos ]
  end lpsig.accum_sig ;
  List.iter begin fun (decl : _ Typing.wpos) ->
    emit @@ `Assoc [ "kind", `String "decl" ;
                     "range", json_of_position decl.pos ]
  end lpsig.decls ;
  let json = `List (List.rev !annots) in
  let out = open_out_bin (file ^ ".json") in
  output_string out (Json.to_string json) ;
  close_out out ;
  Printf.printf "LPSIG: %s -> %s.json\n%!" file file ;
  let html_file = base ^ ".lp.html" in
  let out = open_out_bin html_file in
  output_string out (lp_template base) ;
  close_out out ;
  Printf.printf "CREATE: %s\n%!" html_file

and process_mod file =
  let base = Filename.chop_suffix file ".mod" in
  let Mod lpmod = Accumulate.read_lpmod base in
  let annots =
    `Assoc [ "kind", `String "name" ;
             "range", json_of_position lpmod.name.pos ] ::
    List.map begin fun (acc : _ Typing.wpos) ->
      `Assoc [ "kind", `String "accum" ;
               "range", json_of_position acc.pos ]
    end lpmod.accum @
    List.map begin fun (cl : _ Typing.wpos) ->
      `Assoc [ "kind", `String "clause" ;
               "range", json_of_position cl.pos ]
    end lpmod.clauses in
  let json = `List annots in
  let out = open_out_bin (file ^ ".json") in
  output_string out (Json.to_string json) ;
  close_out out ;
  Printf.printf "LPMOD: %s -> %s.json\n%!" file file

and process_thm file =
  let base = Filename.chop_suffix file ".thm" in
  let (specs, deps) = Depend.thm_dependencies base in
  let deps = specs @ List.rev_map (fun f -> f ^ ".thm") deps in
  Hashtbl.replace dep_tab file deps ;
  List.iter process deps

and process_directory dir =
  let fs = Sys.readdir dir in
  Array.fast_sort String.compare fs ;
  Array.iter (fun file -> process (Filename.concat dir file)) fs

let main () =
  Arg.parse options add_input_file usage_message ;
  input_files := List.rev !input_files ;
  List.iter process !input_files ;
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
    let cmd = Printf.sprintf "%s -nr -a %s.thm -o %s.json -c %s.thc"
        !abella root root root in
    Printf.printf "RUN: %s\n%!" cmd ;
    if Sys.command cmd != 0 then
      failwithf "ERROR running: %s" cmd ;
    let htmlfile = root ^ ".html" in
    let ch = open_out_bin htmlfile in
    output_string ch (thm_template root) ;
    close_out ch ;
    Printf.printf "CREATE: %s\n%!" htmlfile
  end (List.rev !topo)

let () = if not !Sys.interactive then main()
