(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2022 Inria (Institut National de Recherche            *)
(*                         en Informatique et en Automatique)               *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

open Term
open Metaterm
open Checks
open Abella_types
open Typing
open Unifyty
open Extensions
open Printf
open Accumulate

let load_path = State.rref (Sys.getcwd ())

let normalize_filename ?(wrt = !load_path) fn =
  if Filename.is_relative fn
  then Filename.concat wrt fn
  else fn

let can_read_specification = State.rref true

let no_recurse = ref false

let interactive = ref true
let switch_to_interactive = ref false
let is_interactive () = !interactive || !switch_to_interactive

let compile_out = ref None
let compile_out_filename = ref ""
let compile_out_temp_filename = ref ""

let lexbuf = ref (Lexing.from_channel ~with_positions:false stdin)

let annotate = ref false

let witnesses = State.rref false

let unfinished_theorems : string list ref = ref []

exception AbortProof

exception UserInterrupt

let output_flush out s =
  output_string out s ; flush out

let eprintf fmt =
  ksprintf begin fun s ->
    output_flush !out s ;
    if !out <> stdout then
      output_flush stderr s
  end fmt

(* Annotations *)

let json_of_position (lft, rgt) =
  let open Lexing in
  if ( lft = Lexing.dummy_pos
       || lft.pos_fname = ""
       || lft.pos_fname <> rgt.pos_fname )
  then `Null else
    `List [
      `Int lft.pos_cnum ;
      `Int lft.pos_bol ;
      `Int lft.pos_lnum ;
      `Int rgt.pos_cnum ;
      `Int rgt.pos_bol ;
      `Int rgt.pos_lnum ;
    ]

module Annot : sig
  type t
  val fresh : string -> t
  val id : t -> int
  val extend : t -> string -> Json.t -> unit
  val commit : t -> unit
  val last_commit_id : unit -> int option
end = struct
  type t = {
    id : int ;
    typ : string ;
    mutable fields : (string * Json.t) list ;
  }
  let id annot = annot.id
  let last_id = ref @@ -1
  let is_first = ref true
  let fresh typ =
    incr last_id ;
    { id = !last_id ; typ ; fields = [] }
  let extend annot key value =
    annot.fields <- (key, value) :: annot.fields
  let last_commit = ref None
  let commit annot =
    if !annotate then begin
      if not !is_first then fprintf !out ",\n" ;
      is_first := false ;
      let json = `Assoc (("id", `Int annot.id) :: ("type", `String annot.typ) :: annot.fields) in
      fprintf !out "%s%!" (Json.to_string json) ;
      if annot.typ != "system_message" then
        last_commit := Some annot
    end
  let last_commit_id () =
    match !last_commit with
    | None -> None
    | Some {id ; _} -> Some id
end

let link_message pos url =
  let ann = Annot.fresh "link" in
  Annot.extend ann "source" @@ json_of_position pos ;
  Annot.extend ann "url" @@ `String url ;
  Annot.commit ann

type severity = Info | Error

let system_message ?(severity=Info) fmt =
  Printf.ksprintf begin fun msg ->
    if !annotate then begin
      let json = Annot.fresh "system_message" in
      Annot.extend json "after" @@ begin
        match Annot.last_commit_id () with
        | None -> `Null
        | Some id -> `Int id
      end ;
      Annot.extend json "severity" @@ `String (
        match severity with
        | Info -> "info"
        | Error -> "error"
      ) ;
      Annot.extend json "message" @@ `String msg ;
      Annot.commit json
    end else begin
      match severity with
      | Info -> fprintf !out "%s\n%!" msg
      | Error -> eprintf "%s\n%!" msg
    end
  end fmt

let system_message_format ?severity fmt =
  Format.kasprintf (system_message ?severity "%s") fmt

(* DAMF *)

module Damf = struct
  let debugf fmt = Extensions.debugf ~dkind:"DAMF" fmt

  include Damf_cids

  let agent = ref ""
  let set_agent ag =
    agent := ag ;
    debugf "damf.agent = %S" !agent

  let enabled = ref false
  let dispatch = ref "/bin/false" (* will be changed by set_dispatch *)
  let set_dispatch =
    let node_needs_checking = ref false in
    fun fn ->
      if not @@ Sys.file_exists fn then
        failwithf "Cannot find %S: does it exist?" fn ;
      if Filename.check_suffix fn ".js" then begin
        if !node_needs_checking then begin
          let ic = Unix.open_process_in "node --version" in
          let version_string = input_line ic in
          close_in ic ;
          if version_string.[0] != 'v' then
            failwithf "Weird version string returned by `node': %S" version_string ;
          match String.split_on_char '.'
                  (String.sub version_string 1
                     (String.length version_string - 1)) with
          | major :: minor :: _ ->
              let major = int_of_string major in
              let minor = int_of_string minor in
              if (major, minor) < (16, 0) then
                failwithf "`node' version %S too old; need 16.0 or later" version_string ;
              node_needs_checking := true
          | _ ->
              failwithf "Cannot parse `node' version string: %S" version_string
        end ;
        dispatch := "node " ^ fn
      end else begin
        if Unix.(stat fn).st_perm land 0o111 = 0 then
          failwithf "Not executable: %S" fn ;
        dispatch := fn
      end ;
      debugf "damf.dispatch = %S" !dispatch

  (** Download a DAG via dispatch *)
  let get_dag cid =
    let temp_dir = Filename.get_temp_dir_name () in
    ignore @@ run_command @@ Printf.sprintf "%s get %s %s" !dispatch cid temp_dir ;
    let file = Filename.concat temp_dir cid ^ ".json" in
    let json = Json.from_file file in
    Unix.unlink file ;
    (* debugf "DAMF dag = @\n%s" (Json.pretty_to_string json) ; *)
    json

  let exporting = ref false
  let export_file_name = ref "/dev/null"
  let set_export_file fname =
    try
      (* [HACK] this tests if the file is writable and empties it out
       * at the same time. *)
      close_out (open_out_bin fname) ;
      Unix.unlink fname ;
      exporting := true ;
      export_file_name := fname
    with _ ->
      failwithf "Failed to create DAMF export file %S" fname

  let input_file = ref "/dev/null"
  let set_input_file fname = input_file := fname

  type thm_id =
    | Local of Json.t (** theorem in the same file that may or may not be published *)
    | Global of string (** published theorem *)

  let thm_map : (id, thm_id) Hashtbl.t = Hashtbl.create 19
  let clear_thm_map () = Hashtbl.clear thm_map
  let register_thm local_name thid = Hashtbl.replace thm_map local_name thid

  let sigma_map : (id, Json.t) Hashtbl.t = Hashtbl.create 19
  let clear_sigma_map () = Hashtbl.clear sigma_map
  let register_sigma name sigma = Hashtbl.replace sigma_map name sigma

  let exports : (id * Json.t) list ref = ref []
  let add_export id payload = exports := (id, payload) :: !exports
  let write_export_file () =
    if !exporting then begin
      debugf "input_file = %S" !input_file ;
      let name = Filename.chop_suffix (Filename.basename !input_file) ".thm" in
      let formulas = Hashtbl.to_seq thm_map |>
                     Seq.filter_map begin function
                     | (name, Local json) -> Some (name, json)
                     | _ -> None
                     end |> List.of_seq in
      let contexts : (string * Json.t) list =
        Hashtbl.to_seq sigma_map |>
        Seq.map begin fun (name, sigma) ->
          (name, `Assoc ["language", `String ("damf:" ^ language_cid) ;
                         "content", sigma])
        end |>
        List.of_seq in
      let json : Json.t = `Assoc [
          "format", `String "collection" ;
          "name", `String name ;
          "elements", `List (List.rev !exports |> List.map snd) ;
          "formulas", `Assoc formulas ;
          "contexts", `Assoc contexts ;
        ] in
      (* debugf "--- EXPORT %s START ---\n%s\n--- EXPORT %s END ---" *)
      (*   !export_file_name *)
      (*   (Json.to_string json) *)
      (*   !export_file_name ; *)
      let oc = open_out_bin !export_file_name in
      Json.pretty_to_channel oc json ;
      close_out oc
    end

  let publish = ref false
  let publish_target = ref "illegal-target"
  let set_publish_target target =
    match target with
    | "local" | "cloud" ->
        publish := true ;
        publish_target := target
    | _ ->
        failwithf "illegal damf-publish target %S; valid values are \"cloud\" or \"local\""
          target

  let do_publish () =
    if !exporting && !publish then begin
      let output =
        run_command @@ Printf.sprintf "%s publish %s %s"
          !dispatch
          !export_file_name
          !publish_target in
      debugf "--- OUTPUT START ---\n%s\n---OUTPUT END ---\n"
        output ;
      let cid = String.split ~test:(function ' ' | '\n' | '\r' -> true | _ -> false) output |> List.last in
      debugf "Published %S as damf:%s" !export_file_name cid ;
      system_message "Published as damf:%s" cid
    end

  let used_lemmas : id list ref = ref []
  let mark_lemma id =
    debugf "marking lemma %s" id ;
    used_lemmas := id :: !used_lemmas
  let reset_lemmas () = used_lemmas := []

  type 'a marked = {
    key : 'a ;
    rep : Json.t ;
    mutable mark : bool ;
  }

  let sigma_types : id marked list ref = ref []
  let sigma_consts : id marked list ref = ref []
  let sigma_defns : id list marked list ref = ref []

  let reset_marks () =
    let reset_mark m = m.mark <- false in
    List.iter reset_mark !sigma_types ;
    List.iter reset_mark !sigma_consts ;
    List.iter reset_mark !sigma_defns

  let add_type a knd =
    showing_types begin fun () ->
      if List.exists (fun m -> m.key = a) !sigma_types then () else
      let rep = Printf.sprintf "Kind %s %s" a (knd_to_string knd) in
      sigma_types := { key = a ; rep = `String rep ; mark = false }
                     :: !sigma_types
    end

  let mark_type a =
    List.iter (fun m -> if m.key = a then m.mark <- true) !sigma_types

  let add_const k ty =
    showing_types begin fun () ->
      if List.exists (fun m -> m.key = k) !sigma_consts then () else
      let rep = Printf.sprintf "Type %s %s" k (ty_to_string ty) in
      sigma_consts := { key = k ; rep = `String rep ; mark = false }
                      :: !sigma_consts
    end

  let mark_const a =
    List.iter (fun m -> if m.key = a then m.mark <- true) !sigma_consts

  let add_defn flav idtys clauses =
    showing_types begin fun () ->
      if List.exists (fun (id, _) ->
          List.exists (fun m -> List.mem id m.key)
            !sigma_defns)
          idtys then () else
      let clauses_rep = List.map begin fun clause ->
          Printf.sprintf "%s := %s"
            (metaterm_to_string clause.head)
            (metaterm_to_string clause.body)
        end clauses |> String.concat "; " in
      let definienda_rep = List.map begin fun (id, ty) ->
          Printf.sprintf "%s : %s" id (ty_to_string ty)
        end idtys |> String.concat ", " in
      let flavor_rep = match flav with Inductive -> "Define" | _ -> "CoDefine" in
      let rep = Printf.sprintf "%s %s by %s"
          flavor_rep definienda_rep clauses_rep in
      sigma_defns := { key = List.map fst idtys ;
                       rep = `String rep ; mark = false }
                     :: !sigma_defns
    end

  let rec mark_ty ty =
    Term.iter_ty begin function
    | Tycons (c, _) -> mark_type c
    | _ -> ()
    end ty

  and mark_term cx tm =
    match observe (hnorm tm) with
    | Var v ->
        mark_ty v.ty ;
        if not @@ Iset.mem v.name cx then
          if Hashtbl.mem Prover.defs_table v.name
          then mark_defn v.name
          else mark_const v.name
    | DB _ -> ()
    | Lam (bs, tm) ->
        let cx = List.fold_left mark_binding cx bs in
        mark_term cx tm
    | App (f, ts) ->
        mark_term cx f ;
        List.iter (mark_term cx) ts
    | Susp _ | Ptr _ -> assert false

  and mark_metaterm cx mt =
    match mt with
    | Eq (s, t) ->
        mark_term cx s ;
        mark_term cx t
    | Pred (p, _) ->
        mark_term cx p
    | Obj _ ->
        bugf "DAMF export cannot yet handle the specification logic"
    | Binding (_, bs, bod) ->
        let cx = List.fold_left mark_binding cx bs in
        mark_metaterm cx bod
    | And (a, b) | Or (a, b) | Arrow (a, b) ->
        mark_metaterm cx a ;
        mark_metaterm cx b
    | True | False -> ()

  and mark_binding cx (v, ty) = mark_ty ty ; Iset.add v cx

  and mark_defn a =
    List.iter begin fun m ->
      if List.mem a m.key then begin
        let oldmark = m.mark in
        m.mark <- true ;
        if not oldmark then begin
          let def = Hashtbl.find Prover.defs_table a in
          Itab.iter (fun _ ty -> mark_ty ty) def.mutual ;
          List.iter begin fun cl ->
            mark_metaterm Iset.empty cl.head ;
            mark_metaterm Iset.empty cl.body ;
          end def.clauses
        end
      end
    end !sigma_defns

  let sigma () : Json.t =
    let get m = if m.mark then Some m.rep else None in
    `List ( List.rev (List.filter_map get !sigma_types) @
            List.rev (List.filter_map get !sigma_consts) @
            List.rev (List.filter_map get !sigma_defns) )
end

(* Input *)

let perform_switch_to_interactive () =
  assert !switch_to_interactive ;
  switch_to_interactive := false ;
  lexbuf := Lexing.from_channel ~with_positions:false stdin ;
  interactive := true ;
  out := stdout ;
  system_message "Switching to interactive mode." ;
  State.Undo.undo ()

let interactive_or_exit () =
  if not !interactive then
    if !switch_to_interactive then
      perform_switch_to_interactive ()
    else
      exit 1

let position_range (p1, p2) =
  let file = p1.Lexing.pos_fname in
  let line = p1.Lexing.pos_lnum in
  let char1 = p1.Lexing.pos_cnum - p1.Lexing.pos_bol in
  let char2 = p2.Lexing.pos_cnum - p1.Lexing.pos_bol in
  if file = "" then
    ""
  else
    sprintf ": file %s, line %d, characters %d-%d" file line char1 char2

let type_inference_error (pos, ct) exp act =
  system_message "Typing error%s." (position_range pos) ;
  match ct with
  | CArg ->
      system_message ~severity:Error
        "Expression has type %s but is used here with type %s.\n%!"
        (ty_to_string act) (ty_to_string exp)
  | CFun ->
      system_message ~severity:Error
        "Expression is applied to too many arguments\n%!"

let teyjus_only_keywords =
  ["closed"; "exportdef"; "import"; "infix"; "infixl"; "infixr"; "local";
   "localkind"; "postfix"; "posfixl"; "prefix"; "prefixr"; "typeabbrev";
   "use_sig"; "useonly"; "sigma"]

let warn_on_teyjus_only_keywords (ktable, ctable) =
  let tokens = List.unique (List.map fst ktable @ List.map fst ctable) in
  let used_keywords = List.intersect tokens teyjus_only_keywords in
  if used_keywords <> [] then
    system_message "Warning: The following tokens are keywords in Teyjus: %s."
      (String.concat ", " used_keywords)

let update_subordination_sign sr sign =
  List.fold_left Subordination.update sr (sign_to_tys sign)

let sanitize_filename fn =
  try begin
    let lpl = String.length !load_path in
    let fnl = String.length fn in
    if fnl + 1 < lpl then raise Not_found ;
    for i = 0 to lpl - 1 do
      if String.unsafe_get !load_path i <> String.unsafe_get fn i then
        raise Not_found
    done ;
    if String.unsafe_get fn lpl <> '/' then raise Not_found ;
    String.sub fn (lpl + 1) (fnl - lpl - 1)
  end with
  | Not_found -> fn

let read_specification name =
  clear_specification_cache () ;
  if !interactive then
    system_message "Reading specification %S." (sanitize_filename name) ;
  let read_sign = get_sign name in
  let () = warn_on_teyjus_only_keywords read_sign in
  let sign' = merge_signs [!sign; read_sign] in
  let sr' = update_subordination_sign !sr read_sign in
  let clauses' = get_clauses ~sr:sr' name in
  (* Any exceptions must have been thrown by now - do actual assignments *)
  sr := sr' ;
  sign := sign' ;
  Prover.add_clauses clauses'


(* Compilation and importing *)

let comp_spec_sign = State.rref ([], [])
let comp_spec_clauses = State.rref []
let comp_content = State.rref []

let debug_spec_sign1 ?(msg="") () =
  let (kt, ct) = !comp_spec_sign in
  Printf.printf "DEBUG: %sspec_ktable = [%s], spec_ctable = [%s]\n"
    (if msg = "" then "" else "[" ^ msg ^ "] ")
    (String.concat "," (List.map fst kt))
    (String.concat "," (List.map fst ct))
let debug_spec_sign ?(msg="") () = ignore msg

let marshal citem =
  match !compile_out with
  | Some cout -> Marshal.to_channel cout citem []
  | None -> ()

let ensure_finalized_specification () =
  if !can_read_specification then begin
    can_read_specification := false ;
    comp_spec_sign := !sign ;
    comp_spec_clauses := !Prover.clauses
  end

let compile citem =
  (* ensure_finalized_specification () ; *)
  comp_content := citem :: !comp_content ;
  match citem with
  | CKind (ids, knd) ->
      List.iter (fun id -> Damf.add_type id knd) ids
  | CType (ids, ty) ->
      List.iter (fun id -> Damf.add_const id ty) ids
  | CDefine (flav, _, idtys, clauses) ->
      Damf.add_defn flav idtys clauses
  | CTheorem (name, tyvars, form, _) ->
      Damf.reset_marks () ;
      Damf.mark_metaterm Iset.empty form ;
      let sigma = Damf.sigma () in
      let context = name ^ "!sigma" in
      Damf.register_sigma context sigma ;
      let form = Format.asprintf "%s: %a"
          (match tyvars with
           | [] -> ""
           | _ -> "[" ^ String.concat "," tyvars ^ "]")
          format_metaterm form in
      let thm_id : Json.t = `Assoc [
          "language", `String ("damf:" ^ Damf.language_cid) ;
          "content", `String form ;
          "context", `List [`String context] ;
        ] in
      Damf.(register_thm name @@ Local thm_id)
  | _ -> ()

let predicates (_ktable, ctable) =
  ctable |>
  List.filter_map begin fun (id, Poly (_, Ty (_, targty))) ->
    if List.mem id [k_member] || targty = oaty then None
    else Some id
  end

let write_compilation () =
  marshal Version.self_digest ;
  marshal Version.version ;
  debug_spec_sign ~msg:"write_compilation" () ;
  marshal !comp_spec_sign ;
  marshal !comp_spec_clauses ;
  marshal (predicates !sign) ;
  marshal (List.rev !comp_content) ;
  begin match !compile_out with
  | Some cout ->
      close_out cout ;
      Sys.rename !compile_out_temp_filename !compile_out_filename
  | None -> () end

let clause_eq (_,c1) (_,c2) = eq c1 c2

let clauses_to_predicates clauses =
  let clauses = List.map snd clauses in
  clauses |>
  List.map clausify |>
  List.concat |>
  List.map (fun (_, h, _) -> term_head_name h) |>
  List.unique

let ensure_valid_import imp_spec_sign imp_spec_clauses imp_predicates =
  let (ktable, ctable) = !sign in
  let (imp_ktable, imp_ctable) = imp_spec_sign in
  let imp_ctable = List.filter begin
      fun (_id, ty) ->
        match ty with
        | Typing.Poly (_, Ty (_, aty)) when aty = propaty -> false
        | _ -> true
    end imp_ctable in

  (* 1. Imported ktable must be a subset of ktable *)
  let missing_types = List.minus imp_ktable ktable in
  let () = if missing_types <> [] then
      failwithf "Imported file makes reference to unknown types: %s"
        (String.concat ", " (List.map fst missing_types))
  in

  (* 2. Imported ctable must be a subset of ctable *)
  let missing_consts = List.minus imp_ctable ctable in
  let () = if missing_consts <> [] then
      failwithf "Imported file makes reference to unknown constants: %s"
        (String.concat ", " (List.map fst missing_consts))
  in

  (* 3. Imported clauses must be a subset of clauses *)
  let missing_clauses =
    List.minus ~cmp:clause_eq imp_spec_clauses !Prover.clauses
  in
  let () = if missing_clauses <> [] then
      failwithf "Imported file makes reference to unknown clauses for: %s"
        (String.concat ", " (clauses_to_predicates missing_clauses))
  in

  (* 4. Clauses for imported predicates must be subset of imported clauses *)
  let extended_clauses =
    List.minus ~cmp:clause_eq
      (List.find_all
         (fun (_,clause) ->
            clausify clause |>
            List.map (fun (_, h, _) -> term_head_name h) |>
            List.exists (fun h -> List.mem h imp_predicates))
         !Prover.clauses)
      imp_spec_clauses
  in
  let () = if extended_clauses <> [] then
      failwithf "Cannot import file since clauses have been extended for: %s"
        (String.concat ", " (clauses_to_predicates extended_clauses))
  in
  ()


let imported = State.rref []

let maybe_make_importable ?(force=false) root =
  let thc = root ^ ".thc" in
  let thm = root ^ ".thm" in
  let force = force || begin
      Sys.file_exists thm && begin
        not (Sys.file_exists thc) || begin
          let thmstat = Unix.stat thm in
          let thcstat = Unix.stat thc in
          thmstat.Unix.st_mtime > thcstat.Unix.st_mtime
        end
      end
    end in
  if not !Sys.interactive && force then begin
    if !no_recurse then
      failwithf "Recursive invocation of Abella prevented with the -nr flag" ;
    let cmd = Printf.sprintf "%s %S -o %S.out -c %S" Sys.executable_name thm root thc in
    let sanitized_cmd = Printf.sprintf "abella %S -o %S.out -c %S"
        (sanitize_filename thm)
        (sanitize_filename root)
        (sanitize_filename thc) in
    system_message "Running: %s.\n%!" sanitized_cmd ;
    if Sys.command cmd <> 0 then
      failwithf "Could not create %S" thc
  end

let replace_atom_term decl _defn_name defn t =
  let ty = tc [] defn in
  let t = Term.abstract decl ty t in
  let rt = Term.app t [defn] in
  (* Printf.printf "Rewrote %s to %s.\n%!" (term_to_string t) (term_to_string rt) ; *)
  rt

let replace_atom_metaterm decl defn_name defn mt =
  let rmt = map_terms (replace_atom_term decl defn_name defn) mt in
  (* Printf.printf "Rewrote %s to %s.\n%!" (metaterm_to_string mt) (metaterm_to_string rmt) ; *)
  rmt

let replace_atom_clause decl defn_name defn cl =
  let head = replace_atom_metaterm decl defn_name defn cl.head in
  let body = replace_atom_metaterm decl defn_name defn cl.body in
  { head ; body }

let replace_atom_compiled decl defn_name defn comp=
  match comp with
  | CTheorem (nm, tyvars, bod, fin) ->
      (* Printf.printf "Trying to rewrite a CTheorem\n%!" ; *)
      CTheorem (nm, tyvars, replace_atom_metaterm decl defn_name defn bod, fin)
  | CDefine (flav, tyvars, definiens, clauses) ->
      if List.mem_assoc defn_name definiens then
        failwithf "There is already a defined atom named %s in import" defn_name ;
      (* Printf.printf "Trying to rewrite a CDefine\n%!" ; *)
      CDefine (flav, tyvars, definiens,
               List.map (replace_atom_clause decl defn_name defn) clauses)
  | CImport (fn, ws) ->
      (* Printf.printf "Trying to rewrite a CImport\n%!" ; *)
      let ws = List.map begin fun (wfrom, wto) ->
          if wto = decl then (wfrom, defn_name)
          else (wfrom, wto)
        end ws in
      CImport (fn, ws)
  | CKind (ids, _knd) ->
      (* Printf.printf "Trying to rewrite a CKind\n%!" ; *)
      if List.mem defn_name ids then
        failwithf "There are declared types named %s in import" defn_name ;
      comp
  | CType (ids, _) ->
      (* Printf.printf "Trying to rewrite a CType\n%!" ; *)
      if List.mem defn_name ids then
        failwithf "There are declared constants named %s in import" defn_name ;
      comp
  | CClose _ ->
      (* Printf.printf "Trying to rewrite a CClose\n%!" ; *)
      comp

let add_lemma name tys thm =
  ignore @@ Prover.add_lemma name tys thm

let import pos filename withs =
  let rec aux filename withs =
    maybe_make_importable filename ;
    if not (List.mem filename !imported) then begin
      imported := filename :: !imported ;
      let file_dir = Filename.dirname (filename :> string) in
      let thc = (filename :> string) ^ ".thc" in
      let file =
        let ch = open_in_bin thc in
        let dig = (Marshal.from_channel ch : Digest.t) in
        let ver = (Marshal.from_channel ch : string) in
        if dig <> Version.self_digest then begin
          system_message
            "Warning: %S was compiled with a different version (%s) of Abella; recompiling...\n%!"
            thc ver ;
          close_in ch ;
          maybe_make_importable ~force:true filename ;
          let ch = open_in_bin thc in
          ignore (Marshal.from_channel ch : Digest.t) ;
          ignore (Marshal.from_channel ch : string) ;
          ch
        end else ch
      in
      let imp_spec_sign = (Marshal.from_channel file : sign) in
      let imp_spec_clauses = (Marshal.from_channel file : clause list) in
      let imp_predicates = (Marshal.from_channel file : string list) in
      let imp_content = (Marshal.from_channel file : compiled list) in
      ensure_valid_import imp_spec_sign imp_spec_clauses imp_predicates ;
      let rec process_decls decls =
        match decls with
        | [] -> ()
        | decl :: decls -> begin
            match decl with
            | CTheorem(name, tys, thm, _) ->
                add_lemma name tys thm ;
                process_decls decls
            | CDefine(flav, tyargs, idtys, clauses) ->
                ignore @@ Prover.register_definition_clauses flav tyargs idtys clauses ;
                process_decls decls
            | CImport(filename, withs) ->
                aux (normalize_filename (Filename.concat file_dir filename)) withs ;
                process_decls decls
            | CKind(ids, knd) ->
                ignore @@ Prover.add_global_types ids knd;
                process_decls decls
            | CType(ids, (Ty(_, aty) as ty)) when aty = propaty-> begin
                (* Printf.printf "Need to instantiate: %s.\n%!" (String.concat ", " ids) ; *)
                let instantiate_id decls id =
                  try begin
                    let open Typing in
                    let pred_name = List.assoc id withs in
                    let pred = UCon (ghost, pred_name, Term.fresh_tyvar ()) in
                    let pred = type_uterm ~sr:!sr ~sign:!sign ~ctx:[] pred in
                    let pred_ty = tc [] pred in
                    tid_ensure_fully_inferred ~sign:!sign (pred_name, pred_ty) ;
                    if ty <> pred_ty then
                      failwithf "Expected type %s:%s, got %s:%s"
                        id (ty_to_string ty)
                        pred_name (ty_to_string pred_ty) ;
                    List.map (replace_atom_compiled id pred_name pred) decls
                  end with Not_found ->
                    failwithf "Missing instantiation for %s" id
                in
                List.fold_left instantiate_id decls ids |>
                process_decls
              end
            | CType(ids,ty) ->
                ignore @@ Prover.add_global_consts (List.map (fun id -> (id, ty)) ids) ;
                process_decls decls
            | CClose(ty_subords) ->
                List.iter
                  (fun (ty, prev) ->
                     let curr = Subordination.subordinates !sr ty in
                     match List.minus curr prev with
                     | [] -> ()
                     | xs ->
                         failwithf
                           "Cannot close %s since it is now subordinate to %s"
                           (aty_to_string ty)
                           (String.concat ", " (List.map aty_to_string xs)))
                  ty_subords ;
                Prover.close_types !sign !Prover.clauses (List.map fst ty_subords) ;
                process_decls decls
          end
      in
      process_decls imp_content
    end
  in
  if List.mem filename !imported then
    system_message "Ignoring import: %s has already been imported." filename
  else begin
    system_message "Importing from %S." (sanitize_filename filename) ;
    aux (normalize_filename filename) withs ;
    link_message pos (filename ^ ".html") ;
  end

let damf_import =
  let open Json in
  let ctx_tab : (id, Json.t) Hashtbl.t = Hashtbl.create 19 in
  let form_tab : (id, Json.t) Hashtbl.t = Hashtbl.create 19 in
  let debugf fmt = Extensions.debugf ~dkind:"DAMF.import" fmt in
  let check_valid_language json =
    let cid = Util.member "language" json |>
              Util.to_string in
    if cid <> Damf.language_cid then
      failwithf "Unexpected language %S@\nExpecting %S"
        cid Damf.language_cid
  in
  let doit cid =
    let process_context_cid cid_json =
      let json = Hashtbl.find ctx_tab (Util.to_string cid_json) in
      check_valid_language json ;
      let content = Util.member "content" json |> Util.to_list in
      List.iter begin fun txt ->
        let txt = Util.to_string txt in
        let lb = Lexing.from_string (txt ^ ".") in
        let cmd, _ = Parser.top_command_start Lexer.token lb in
        let remark = ref "" in
        let () = match cmd with
          | Kind (ids, knd) ->
              let fresh_ids = Prover.add_global_types ids knd in
              remark :=
                if fresh_ids = [] then " (* merged *)"
                else Printf.sprintf " (* fresh: %s *)" (String.concat ", " fresh_ids) ;
              compile (CKind (ids, knd)) ;
              debug_spec_sign ~msg:"Kind" ()
          | Type (ids, ty) ->
              let fresh_ids = Prover.add_global_consts (List.map (fun id -> (id, ty)) ids) in
              remark :=
                if fresh_ids = [] then " (* merged *)"
                else Printf.sprintf " (* fresh: %s *)" (String.concat ", " fresh_ids) ;
              compile (CType (ids, ty)) ;
              debug_spec_sign ~msg:"Type" ()
          | Define (flav, tyargs, udefs) -> begin
              match Prover.register_definition flav tyargs udefs with
              | None -> remark := " (* merged *)"
              | Some comp -> compile comp
            end
          | _ ->
              failwithf "Illegal element in Sigma: %s" txt
        in
        debugf "%s.%s" (top_command_to_string cmd) !remark
      end content
    in
    let process_theorem_cid thmname cid =
      let json = Hashtbl.find form_tab cid in
      check_valid_language json ;
      let () = Util.member "context" json |>
               Util.to_list |>
               List.iter process_context_cid in
      let txt = Util.member "content" json |> Util.to_string in
      let txt =
        Printf.sprintf "Theorem %s%s%s." thmname
          (match txt.[0] with
           | ':' | '[' -> "" | _ -> ": ")
          txt
      in
      let lb = Lexing.from_string txt in
      let cmd, _ = Parser.top_command_start Lexer.token lb in
      match cmd with
      | Theorem (name, tys, thm) -> begin
          let thm = type_umetaterm ~sr:!sr ~sign:!sign thm in
          check_theorem tys thm ;
          (* Prover.theorem thm ; *)
          add_lemma name tys thm ;
          compile (CTheorem (name, tys, thm, Finished)) ;
          Damf.(register_thm name (Global cid)) ;
          debugf "%s." (top_command_to_string cmd)
        end
      | _ ->
          bugf "Parsed a non-theorem from a generated `Theorem' text"
    in
    let process_assertion json =
      let statement = Util.member "claim" json in
      match Util.member "format" statement |> Util.to_string with
      | "annotated-production" ->
          let thmname =
            match Util.member "annotation" statement with
            | `List (nm :: _) -> Util.to_string nm
            | `Assoc _ as asc -> Util.member "name" asc |> Util.to_string
            | `String nm -> nm
            | ann ->
                failwithf "Cannot process annotation: %s" (Json.to_string ann)
          in
          statement |>
          Util.member "production" |>
          Util.member "sequent" |>
          Util.member "conclusion" |> Util.to_string |>
          process_theorem_cid thmname
      | "production" ->
          debugf "Ignoring anonymous production"
      | fmt ->
          failwithf "Expecting format \"annotated-production\",\ found %S" fmt
    in
    let process_element json =
      match Util.member "format" json |> Util.to_string with
      | "assertion" -> process_assertion (Util.member "element" json)
      | "annotated-sequent" ->
          let thmname =
            match Util.member "annotation" json |> Util.to_list with
            | nm :: _ -> Util.to_string nm
            | _ -> failwithf "Expecting lemma name, found empty annotation list"
          in
          json |>
          Util.member "sequent" |>
          Util.member "conclusion" |> Util.to_string |>
          process_theorem_cid thmname
      | fmt ->
          failwithf "Expecting format \"assertion\" or \"annotated-sequent\", found %S" fmt
    in
    let dag = Damf.get_dag cid in
    match Util.member "format" dag |> Util.to_string with
    | "collection" ->
        let read_into_table tab json =
          Hashtbl.clear tab ;
          let assoc = Json.Util.to_assoc json in
          List.iter (fun (k, v) -> Hashtbl.replace tab k v) assoc
        in
        read_into_table ctx_tab (Util.member "contexts" dag) ;
        debugf "Loaded contexts" ;
        read_into_table form_tab (Util.member "formulas" dag) ;
        debugf "Loaded formulas" ;
        let elements = Util.member "elements" dag |> Util.to_list in
        List.iter process_element elements ;
        debugf "Loaded elements"
    | fmt ->
        debugf "Expecting format \"collection\", found %S" fmt ;
        failwithf "Invalid JSON: expecting key \"format\""
    | exception Util.Type_error (nm, t) ->
        debugf "Invalid JSON@\n%a@\n%s: %s" pp dag nm (Json.pretty_to_string t) ;
        failwithf "Invalid JSON: expecting key \"format\""
  in
  fun cid ->
    try doit cid with
    | Parser.Error ->
        failwithf "Parse error in import of damf:%s" cid
    | Util.Type_error (nm, t) ->
        debugf "Invalid JSON@\n%s: %s" nm (Json.pretty_to_string t) ;
        failwithf "Parse error in import of damf:%s" cid

let damf_extract_conclusion cid : damf_cid =
  let open Json in
  (* let dkind = "DAMF.ImportAs" in *)
  let handle_production dag =
    (* debugf ~dkind "handle_production@\n%s" (Json.pretty_to_string dag) ; *)
    dag |> Util.member "sequent" |> Util.member "conclusion" |> Util.to_string
  in
  let handle_annotated_production dag =
    (* debugf ~dkind "handle_annotated_production@\n%s" (Json.pretty_to_string dag) ; *)
    dag |> Util.member "production" |> handle_production
  in
  let handle_assertion dag =
    (* debugf ~dkind "handle_assertion@\n%s" (Json.pretty_to_string dag) ; *)
    let claim = Util.member "claim" dag in
    match Util.member "format" claim |> Util.to_string with
    | "production" -> handle_production claim
    | "annotated-production" -> handle_annotated_production claim
    | format ->
        failwithf "Expecting format \"annotated-production\" or \"production\", found %S" format
  in
  let dag = Damf.get_dag cid in
  match Util.member "format" dag |> Util.to_string with
  | "assertion" -> Util.member "assertion" dag |> handle_assertion
  | "production" -> Util.member "production" dag |> handle_production
  | "annotated-production" -> Util.member "content" dag |> handle_annotated_production
  | format ->
      failwithf "Expecting format \"assertion\" or \"[annotated-]production\", found %S" format

let format_kind ff (Knd arity) =
  let rec aux n =
    if n = 0 then Format.pp_print_string ff "type" else begin
      Format.pp_print_string ff "type -> " ;
      aux (n - 1)
    end
  in
  aux arity

let damf_export_theorem name =
  if not !Damf.exporting then () else
    showing_types begin fun () ->
      (* let dkind = "DAMF" in *)
      let lemmas = List.map begin fun locid ->
          match Hashtbl.find Damf.thm_map locid with
          | Damf.Local _ -> `String locid
          | Damf.Global cid -> `String ("damf:" ^ cid)
          | exception Not_found ->
              bugf "used lemma %S not found in Damf.thm_map" locid
        end !Damf.used_lemmas in
      let json : Json.t =
        `Assoc [
          "format", `String "assertion" ;
          "element", `Assoc [
            "agent", `String !Damf.agent ;
            "claim", `Assoc [
              "format", `String "annotated-production" ;
              "annotation", `List [`String name] ;
              "production", `Assoc [
                "mode", `String ("damf:" ^ Damf.tool_cid) ;
                "sequent", `Assoc [
                  "conclusion", `String name ;
                  "dependencies", `List lemmas ;
                ] ;
              ] ;
            ] ;
          ] ;
        ] in
      (* debugf ~dkind "--- THEOREM START ---\n%S: %s\n--- THEOREM END ---" *)
      (*   name (Json.to_string json) ; *)
      Damf.add_export name json
    end

let damf_export_manual_adapter external_cid name =
  if not !Damf.exporting then () else
    showing_types begin fun () ->
      let json : Json.t =
        `Assoc [
          "format", `String "assertion" ;
          "element", `Assoc [
              "agent", `String !Damf.agent ;
              "claim", `Assoc [
                "format", `String "annotated-production" ;
                "annotation", `List [`String name] ;
                "production", `Assoc [
                  "mode", `Null ;
                  "sequent", `Assoc [
                    "conclusion", `String name ;
                    "dependencies", `List [ `String ("damf:" ^ external_cid) ] ;
                  ] ;
                ] ;
              ] ;
            ] ;
        ] in
      (* debugf ~dkind:"DAMF" "--- ADAPTER START ---\n%S: %s\n--- ADAPTER END ---" *)
      (*   name (Json.to_string json) ; *)
      Damf.add_export (name ^ "!" ^ "adapted") json
    end

(* Proof processing *)

let query q =
  let fv = ids_to_fresh_tyctx (umetaterm_extract_if is_capital_name q) in
  let ctx = fresh_alist ~tag:Logic ~used:[] fv in
  match type_umetaterm ~sr:!sr ~sign:!sign ~ctx (UBinding(Metaterm.Exists, fv, q)) with
  | Binding(Metaterm.Exists, fv, q) ->
      let support = metaterm_support q in
      let ctx = Tactics.fresh_nameless_alist ~support ~ts:0 ~tag:Logic fv in
      let q = replace_metaterm_vars ctx q in
      let _ = Tactics.search q
          ~depth:!Prover.search_depth
          ~hyps:[]
          ~clauses:!Prover.clauses
          ~def_unfold:Prover.def_unfold
          ~retype:Prover.retype
          ~sr:!sr
          ~sc:(fun _w ->
              system_message "Found solution:" ;
              List.iter
                (fun (n, v) ->
                   system_message "%s = %s" n (term_to_string v))
                ctx ;
              if !interactive then fprintf !out "\n%!")
      in
      system_message "No more solutions."
  | _ -> assert false

let set_fail ~key ~expected v =
  failwithf "Unknown value '%s' for key %S; expected %s"
    (set_value_to_string v) key expected

let set_subgoal_max_spec spec =
  let buf = Lexing.from_string spec in
  let spec = Parser.depth_spec Lexer.token buf in
  Prover.set_subgoal_max spec

let set k v =
  match k, v with
  | "subgoals", Int d when d >= 0 ->
      Prover.reset_subgoal_max () ;
      Prover.set_subgoal_max [d, Some max_int]
  | "subgoals", Str "on" ->
      Prover.reset_subgoal_max () ;
      Prover.set_subgoal_max_default max_int
  | "subgoals", Str "off" ->
      Prover.reset_subgoal_max () ;
      Prover.set_subgoal_max_default 0
  | "subgoals", QStr spec ->
      set_subgoal_max_spec spec
  | "subgoals", _ -> set_fail v
                       ~key:"subgoals"
                       ~expected:"'on', 'off', non-negative integer, or depth specification"

  | "instantiations", Str "on" -> Prover.show_instantiations := true
  | "instantiations", Str "off" -> Prover.show_instantiations := false
  | "instantiations", _ -> set_fail v
                             ~key:"instantiations"
                             ~expected:"'on' or 'off'"

  | "types", Str "on" -> Term.show_types := true
  | "types", Str "off" -> Term.show_types := false
  | "types", _ -> set_fail v
                    ~key:"types"
                    ~expected:"'on' or 'off'"

  | "nominal_types", Str "on" ->  Metaterm.show_nominal_types := true
  | "nominal_types", Str "off" -> Metaterm.show_nominal_types := false
  | "nominal_types", _ -> set_fail v
                            ~key:"nominal_types"
                            ~expected:"'on' or 'off'"

  | "search_depth", Int d when d >= 0 -> Prover.search_depth := d
  | "search_depth", _ -> set_fail v
                           ~key:"search_depth"
                           ~expected:"non-negative integer"

  | "witnesses", Str "on" -> witnesses := true
  | "witnesses", Str "off" -> witnesses := false
  | "witnesses", _ -> set_fail v
                        ~key:"witnesses"
                        ~expected:"'on' or 'off'"

  | "load_path", QStr s -> load_path := normalize_filename ~wrt:(Sys.getcwd ()) s

  | _, _ -> failwithf "Unknown key '%s'" k

let handle_search_witness w =
  if !witnesses then
    system_message "Witness: %s." (witness_to_string w)

let term_witness (_t, w) =
  if !witnesses then
    system_message "Witness: %s." (witness_to_string w)

let suppress_proof_state_display = State.rref false

type processing_state =
  | Process_top
  | Process_proof of proof_processor

and proof_processor = {
  id : int ;
  thm : string ;
  compile : (fin -> unit) ;
  reset : (unit -> unit) ;
}

let current_state = State.rref Process_top

let print_clauses () =
  List.iter print_clause !Prover.clauses

let rec process1 () =
  State.Undo.push () ;
  try begin match !current_state with
    | Process_top -> process_top1 ()
    | Process_proof proc -> begin
        try process_proof1 proc with
        | Prover.End_proof reason -> begin
            system_message "Proof %s" begin
              match reason with
              | `completed fin -> begin
                  proc.compile fin ;
                  if fin = Unfinished then
                    unfinished_theorems := proc.thm :: !unfinished_theorems ;
                  Printf.sprintf "completed%s"
                    (match fin with
                     | Finished -> ""
                     | Unfinished -> " *** USING skip ***")
                end
              | `aborted -> "ABORTED"
            end ;
            proc.reset () ;
            (* print_clauses () ; *)
            current_state := Process_top
          end
      end
  end with
  | Abella_types.Reported_parse_error ->
      State.Undo.undo () ;
      Lexing.flush_input !lexbuf ;
      interactive_or_exit ()
  | Parser.Error ->
      State.Undo.undo () ;
      system_message ~severity:Error
        "Syntax error%s.\n%!" (position !lexbuf) ;
      Lexing.flush_input !lexbuf ;
      interactive_or_exit ()
  | TypeInferenceFailure(exp, act, ci) ->
      State.Undo.undo () ;
      type_inference_error ci exp act ;
      interactive_or_exit ()
  | End_of_file ->
      write_compilation () ;
      Damf.write_export_file () ;
      Damf.do_publish () ;
      if !switch_to_interactive then begin
        perform_switch_to_interactive ()
      end else begin
        match !current_state with
        | Process_top ->
            if not (is_interactive ()) && !unfinished_theorems <> [] then begin
              system_message "There were skips in these theorem(s): %s\n"
                (String.concat ", "  !unfinished_theorems)
            end ;
            if !annotate then fprintf !out "]\n%!" ;
            exit 0
        | _ ->
            system_message ~severity:Error "Proof NOT Completed." ;
            if !annotate then fprintf !out "]\n%!" ;
            exit 1
      end
  | e ->
      State.Undo.undo () ;
      let msg = match e with
        | Failure msg -> msg
        | Unify.UnifyFailure fl -> Unify.explain_failure fl
        | Unify.UnifyError err -> Unify.explain_error err
        | UserInterrupt -> "Interrupted (use Ctrl-D to quit)"
        | _ ->
            Printexc.to_string e ^ "\n\n\
                                   \ Sorry for displaying a naked OCaml exception. An informative error message\n\
                                   \ has not been designed for this situation.\n\n\
                                   \ To help improve Abella's error messages, please file a bug report at\n\
                                   \ <https://github.com/abella-prover/abella/issues>. Thanks!"
      in
      system_message ~severity:Error "Error: %s\n%!" msg ;
      interactive_or_exit ()


and process_proof1 proc =
  let annot = Annot.fresh "proof_command" in
  if not !suppress_proof_state_display then begin
    if !annotate then begin
      Annot.extend annot "thm_id" @@ `Int proc.id ;
      Annot.extend annot "theorem" @@ `String proc.thm ;
      Annot.extend annot "start_state" @@ Prover.state_json () ;
    end
    else if !interactive then Prover.display !out
  end ;
  suppress_proof_state_display := false ;
  if !interactive && not !annotate then fprintf !out "%s < %!" proc.thm ;
  let input, input_pos = Parser.command_start Lexer.token !lexbuf in
  let cmd_string = command_to_string input in
  if not (!interactive || !annotate) then fprintf !out "%s.\n%!" cmd_string ;
  if !annotate then Annot.extend annot "command" @@ `String cmd_string ;
  if !annotate && fst input_pos != Lexing.dummy_pos then
    Annot.extend annot "range" @@ json_of_position input_pos ;
  let damf_mark h =
    match h with
    | Remove (name, _) | Keep (name, _) ->
        if not @@ Prover.is_hyp name then Damf.mark_lemma name
  in
  let perform () =
    begin match input with
    | Induction(args, hn) -> Prover.induction ?name:hn args
    | CoInduction hn -> Prover.coinduction ?name:hn ()
    | Apply(depth, h, args, ws, hn ) -> begin
        damf_mark h ;
        Prover.apply ?depth ?name:hn h args ws ~term_witness
      end
    | Backchain(depth, h, ws) -> begin
        damf_mark h ;
        Prover.backchain ?depth h ws ~term_witness
      end
    | Cut(h, arg, hn) -> begin
        damf_mark h ;
        Prover.cut ?name:hn h arg ;
      end
    | CutFrom(h, arg, t, hn) -> begin
        damf_mark h ;
        Prover.cut_from ?name:hn h arg t
      end
    | SearchCut(h, hn) -> begin
        damf_mark h ;
        Prover.search_cut ?name:hn h
      end
    | Inst(h, ws, hn) -> begin
        damf_mark h ;
        Prover.inst ?name:hn h ws
      end
    | Case(str, hn) -> begin
        damf_mark str ;
        Prover.case ?name:hn str
      end
    | Assert(t, dp, hn) -> begin
        untyped_ensure_no_restrictions t ;
        Prover.assert_hyp ?name:hn ?depth:dp t
      end
    | Monotone(h, t, hn) -> begin
        damf_mark h ;
        Prover.monotone ?name:hn h t
      end
    | Exists(_, ts) -> List.iter Prover.exists ts
    | Clear(cm, hs) -> Prover.clear cm hs
    | Abbrev(hs, s) -> Prover.abbrev (Iset.of_list hs) s
    | Unabbrev(hs) -> Prover.unabbrev (Iset.of_list hs)
    | Rename(hfr, hto) -> Prover.rename hfr hto
    | Search(bounds) -> begin
        let depth = match bounds with
          | `depth n -> Some n
          | _ -> None
        in
        let witness = match bounds with
          | `witness w -> w
          | _ -> WMagic
        in
        Prover.search ?depth ~witness ~handle_witness:handle_search_witness ()
      end
    | Async_steps -> Prover.async ()
    | Permute(ids, h) -> Prover.permute_nominals ids h
    | Split -> Prover.split false
    | SplitStar -> Prover.split true
    | Left -> Prover.left ()
    | Right -> Prover.right ()
    | Unfold (cs, ss) -> Prover.unfold cs ss
    | Intros hs -> Prover.intros hs
    | Skip -> Prover.skip ()
    | Abort -> raise (Prover.End_proof `aborted)
    | Undo | Common(Back) -> begin
        if !interactive then State.Undo.back 2
        else failwith "Cannot use interactive commands in non-interactive mode"
      end
    | Common(Reset) -> begin
        if !interactive then State.Undo.reset ()
        else failwith "Cannot use interactive commands in non-interactive mode"
      end
    | Common(Set(k, v)) -> set k v
    | Common(Show nm) -> begin
        system_message_format "%t" (Prover.show nm) ;
        if !interactive then fprintf !out "\n%!" ;
        suppress_proof_state_display := true
      end
    | Common(Quit) -> raise End_of_file
    end
  in
  if not !annotate then perform () else
  match perform () with
  | () ->
      Annot.extend annot "end_state" @@ Prover.state_json () ;
      Annot.commit annot
  | exception e ->
      Annot.commit annot ;
      raise e

and process_top1 () =
  if !interactive && not !annotate then fprintf !out "Abella < %!" ;
  let annot = Annot.fresh "top_command" in
  let input, input_pos = Parser.top_command_start Lexer.token !lexbuf in
  if fst input_pos != Lexing.dummy_pos then
    Annot.extend annot "range" @@ json_of_position input_pos ;
  let cmd_string = top_command_to_string input in
  if not (!interactive || !annotate) then fprintf !out "%s.\n%!" cmd_string ;
  Annot.extend annot "command" @@ `String cmd_string ;
  Annot.commit annot ;
  begin match input with
  | Theorem(name, tys, thm) -> begin
      let st = get_bind_state () in
      let seq = Prover.copy_sequent () in
      let thm = type_umetaterm ~sr:!sr ~sign:!sign thm in
      check_theorem tys thm ;
      Prover.theorem thm ;
      let oldsign = !sign in
      let thm_compile fin =
        sign := oldsign ;
        compile (CTheorem(name, tys, thm, fin)) ;
        damf_export_theorem name ;
        add_lemma name tys thm
      in
      let thm_reset () =
        sign := oldsign ;
        Prover.reset_prover st seq ()
      in
      Prover.start_proof () ;
      Damf.reset_lemmas () ;
      current_state := Process_proof {
          id = Annot.id annot ; thm = name ;
          compile = thm_compile ;
          reset = thm_reset
        }
    end
  | SSplit(name, names) ->
      let gen_thms = Prover.create_split_theorems name names in
      List.iter begin fun (n, (tys, t)) ->
        system_message_format "%t" (Prover.print_theorem n (tys, t)) ;
        add_lemma n tys t ;
        compile (CTheorem(n, tys, t, Finished))
      end gen_thms ;
  | Define (flav, tyargs, udefs) ->
      Option.iter compile @@ Prover.register_definition flav tyargs udefs
  | TopCommon(Back) ->
      if !interactive then State.Undo.back 2
      else failwith "Cannot use interactive commands in non-interactive mode"
  | TopCommon(Reset) ->
      if !interactive then State.Undo.reset ()
      else failwith "Cannot use interactive commands in non-interactive mode"
  | TopCommon(Set(k, v)) -> set k v
  | TopCommon(Show(n)) -> system_message_format "%t" (Prover.show n)
  | TopCommon(Quit) -> raise End_of_file
  | Import(imp, pos, withs) -> begin
      match imp with
      | LocalFile filename ->
          compile (CImport (filename, withs)) ;
          import pos filename withs
      | DamfCid cid ->
          if not !Damf.enabled then
            failwithf "Cannot process DAMF imports without --damf-imports" ;
          if withs <> [] then
            failwithf "Importing from DAMF with propositional instantiation is not supported" ;
          damf_import cid
    end
  | ImportAs(cid, _, name, tys, body) -> begin
      let thm = type_umetaterm ~sr:!sr ~sign:!sign body in
      check_theorem tys thm ;
      let fin =
        if !Damf.enabled then begin
          let conclusion_cid = damf_extract_conclusion cid in
          damf_export_manual_adapter conclusion_cid name ;
          Finished
        end else begin
          system_message "Running without --damf-imports; trusting theorem." ;
          Unfinished
        end
      in
      compile (CTheorem(name, tys, thm, fin)) ;
      add_lemma name tys thm ;
    end
  | Specification(filename, pos) ->
      if !can_read_specification then begin
        read_specification (normalize_filename filename) ;
        ensure_finalized_specification () ;
        if !annotate then link_message pos (filename ^ ".html") ;
      end else
        failwith "Specification can only be read \
                 \ at the begining of a development."
  | Query(q) -> query q
  | Kind(ids,knd) ->
      (* check_noredef ids; *)
      ignore @@ Prover.add_global_types ids knd;
      compile (CKind (ids,knd)) ;
      List.iter (fun id -> Damf.add_type id knd) ids ;
      debug_spec_sign ~msg:"Kind" ()
  | Type(ids, ty) ->
      (* check_noredef ids; *)
      ignore @@ Prover.add_global_consts (List.map (fun id -> (id, ty)) ids) ;
      compile (CType(ids, ty)) ;
      List.iter (fun id -> Damf.add_const id ty) ids ;
      debug_spec_sign ~msg:"Type" ()
  | Close(atys) ->
      Prover.close_types !sign !Prover.clauses atys ;
      compile (CClose(List.map (fun aty -> (aty, Subordination.subordinates !sr aty)) atys))
  end ;
  if !interactive then flush stdout ;
  if not !annotate then fprintf !out "\n%!"

(* Command line and startup *)

let welcome_msg = sprintf "Welcome to Abella %s.\n" Version.version

let usage_message = Printf.sprintf "%s [options] <theorem-file>" begin
    if !Sys.interactive then "abella" else Filename.basename Sys.executable_name
  end

let set_output filename =
  out := open_out filename

let set_compile_out filename =
  compile_out_filename := filename ;
  let (fn, ch) = Filename.open_temp_file
      ~mode:[Open_binary]
      ~temp_dir:(Filename.dirname filename)
      (Filename.basename filename) ".part" in
  compile_out_temp_filename := fn ;
  compile_out := Some ch

let makefile = ref false

let parse_value v =
  if String.length v < 1 then bugf "parse_value" ;
  match v.[0] with
  | '0' .. '9' -> Int (int_of_string v)
  | '"' -> QStr (String.sub v 1 (String.length v - 2))
  | _ -> Str v

let set_flags flagstr =
  try begin
    flagstr |>
    String.split ~test:(fun c -> c = ',') |>
    List.map (String.split ~test:(fun c -> c = '=')) |>
    List.iter begin function
    | [k ; v] -> set k (parse_value v)
    | [k]     -> set k (Str "on")
    | _       -> bugf "set_flags: %S" flagstr
    end
  end with
  | Invalid_argument msg | Failure msg ->
      raise (Arg.Bad msg)
  | e ->
      raise (Arg.Bad (Printexc.to_string e))

let print_version () =
  print_endline Version.version ;
  exit 0

let options =
  Arg.align [
    "-f", Arg.String set_flags,
    "<flags> Initialize flags based on a comma-separate list of key=value pairs" ;

    "-i", Arg.Set switch_to_interactive,
    " Switch to interactive mode after reading inputs" ;

    "-o", Arg.String set_output, "<file-name> Output to file" ;

    "-c", Arg.String set_compile_out,
    "<file-name> Compile definitions and theorems in an importable format" ;

    "-a", Arg.Set annotate, " Annotate mode" ;

    "--damf-agent", Arg.String Damf.set_agent, "AG Set the DAMF agent profile to AG" ;
    "--damf-profile", Arg.String Damf.set_agent, "AG Same as --damf-agent AG" ;
    "--damf-imports", Arg.Set Damf.enabled, " Enable DAMF imports" ;
    "--damf-dispatch-prog", Arg.String Damf.set_dispatch, "<prog> Path to the `dispatch' tool" ;
    "--damf-publish-file", Arg.String Damf.set_export_file, "FILE Set DAMF export file to FILE" ;
    "--damf-publish", Arg.String Damf.set_publish_target, "TARGET Run `dispatch publish' with target TARGET (cloud, local)" ;

    "-nr", Arg.Set no_recurse, " Do not recursively invoke Abella" ;

    "-v", Arg.Unit print_version, " Show version and exit" ;

    "-M", Arg.Set makefile, " Output dependencies in Makefile format" ;
  ]

let input_files = ref []

let set_input () =
  match !input_files with
  | [] -> ()
  | [filename] ->
      if not @@ String.ends_with ~suffix:".thm" filename then
        failwithf "Invalid input file name %S: does not end in .thm"
          filename ;
      interactive := false ;
      Damf.set_input_file filename ;
      lexbuf := lexbuf_from_file filename ;
      load_path := normalize_filename ~wrt:(Sys.getcwd ()) (Filename.dirname filename)
  | fs ->
      system_message ~severity:Error
        "Error: Multiple files specified as input: %s.\n%!"
        (String.concat ", " fs) ;
      exit 1

let add_input filename =
  input_files := !input_files @ [filename]

let () = try
    Sys.set_signal Sys.sigint
      (Sys.Signal_handle (fun _ -> raise UserInterrupt)) ;

    let config_home =
      try Sys.getenv "XDG_CONFIG_HOME"
      with Not_found -> Filename.concat (Sys.getenv "HOME") ".config"
    in
    let config_dir = Filename.concat config_home "abella" in
    let config_json = Filename.concat config_dir "config.json" in
    if Sys.file_exists config_json then begin
      Json.from_file config_json |>
      Json.Util.to_assoc |>
      List.iter begin fun (key, value) ->
        match key with
        | "damf.agent"
        | "damf.profile" -> begin
            match Json.Util.to_string_option value with
            | Some ag ->
                Damf.set_agent ag
            | None ->
                failwithf "Invalid value for config option damf.agent (file %S)"
                  config_json
          end
        | "damf.dispatch" -> begin
            match Json.Util.to_string_option value with
            | Some prog ->
                Damf.set_dispatch prog
            | None ->
                failwithf "Invalid value for config option damf.dispatch (file %S)"
                  config_json
          end
        | _ ->
            Printf.eprintf "Warning: ignoring config key %S in %S" key config_json
      end
    end ;

    if not !Sys.interactive then begin
      Arg.parse options add_input usage_message ;

      if !makefile then begin
        List.iter Depend.print_deps !input_files ;
      end else begin
        if !Damf.enabled then begin
          interactive := false ;
          switch_to_interactive := false ;
          if !input_files = [] then
            failwithf "DAMF support is currently only enabled in batch mode" ;
          if !Damf.publish && not !Damf.exporting then begin
            let export_file = List.hd !input_files ^ ".json" in
            debugf ~dkind:"DAMF" "exporting to %S" export_file ;
            Damf.set_export_file export_file
          end
        end ;
        set_input () ;
        if !annotate then fprintf !out "[%!" ;
        if !interactive then system_message "%s" welcome_msg ;
        State.Undo.set_enabled @@ is_interactive () ;
        while true do process1 () done
      end
    end
  with
  | Failure msg ->
      Printf.eprintf "FAILURE: %s\n" msg ; exit 1
;;
