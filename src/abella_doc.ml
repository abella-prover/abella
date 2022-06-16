(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Generate documentation for a collection of Abella .thm files *)

open Extensions

let compact = ref false

let abella = ref "abella"

let options = Arg.[
    "-a", Set_string abella, "PROG Run PROG instead of the command 'abella'" ;
    "-c", Set compact, " Compact mode" ;
  ] |> Arg.align

let input_files : string list ref = ref []

let add_input_file file =
  input_files := file :: !input_files

let usage_message = Printf.sprintf "%s [options] <theorem-file> ..." begin
    if !Sys.interactive then "abella_doc" else Filename.basename Sys.executable_name
  end

let main () =
  Arg.parse options add_input_file usage_message ;
  let dep_tab = Hashtbl.create (List.length !input_files) in
  List.iter begin fun thmfile ->
    match Filename.chop_suffix thmfile ".thm" with
    | exception Invalid_argument _ ->
      failwithf "Invalid file %S; All input files must end in .thm" thmfile
    | base ->
      if not (Hashtbl.mem dep_tab thmfile) then
        let (_, deps) = Depend.get_thm_depend base in
        let deps = List.map begin fun dep ->
            Filename.concat (Filename.dirname thmfile) dep
          end deps in
        Hashtbl.replace dep_tab base deps
  end !input_files ;
  let seen = Hashtbl.create (List.length !input_files) in
  let topo = ref [] in
  let rec toproc file =
    if Hashtbl.mem seen file then () else begin
      Hashtbl.replace seen file () ;
      List.iter toproc (Hashtbl.find dep_tab file) ;
      topo := file :: !topo ;
    end in
  Hashtbl.iter (fun f _ -> toproc f) dep_tab ;
  (* topo := [] ; *)
  (* Hashtbl.iter (fun f _ -> topo := f :: !topo) dep_tab ; *)
  List.iter begin fun thmfile ->
    (* let deps = Hashtbl.find dep_tab thmfile in *)
    (* Printf.printf "%s: %s\n" thmfile (String.concat " " deps) ; *)
    let cmd = Printf.sprintf "%s -nr -a %s.thm -o %s.json -c %s.thc"
        !abella thmfile thmfile thmfile in
    Printf.printf "$ %s\n%!" cmd ;
    if Sys.command cmd != 0 then
      failwithf "ERROR running: %s" cmd
  end (List.rev !topo)

let () = if not !Sys.interactive then main()
