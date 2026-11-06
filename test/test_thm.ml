(****************************************************************************)
(* Copyright (C) 2026 Inria (Institut National de Recherche                 *)
(*                           en Informatique et en Automatique)             *)
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

(* Tests for .thm sources, specifications, imports, and .thc artifacts. *)

open Abella_lib
open Abella_types
open Extensions
open Term
open Typing
open Test_helper

module D = Abella_driver

let processing_state = ref D.Process_top

let read_file path =
  let ch = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ch) begin fun () ->
    really_input_string ch (in_channel_length ch)
  end

let write_file path contents =
  let ch = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out ch) begin fun () ->
    output_string ch contents
  end

let rec remove_tree path =
  if Sys.is_directory path then begin
    Array.iter (fun name -> remove_tree (Filename.concat path name))
      (Sys.readdir path) ;
    Unix.rmdir path
  end else
    Sys.remove path

let with_temp_dir f =
  let dir = Filename.temp_file "abella-thm-test" "" in
  Sys.remove dir ;
  Unix.mkdir dir 0o700 ;
  Fun.protect ~finally:(fun () -> remove_tree dir) (fun () -> f dir)

let start_thm_session () =
  State.reload D.initial_snapshot ;
  processing_state := D.Process_top ;
  State.Undo.set_enabled true ;
  State.Undo.reset () ;
  Accumulate.clear_specification_cache () ;
  Source.clear_virtual () ;
  Source.clear_thc_trust () ;
  D.Setup.compiling := [] ;
  D.Setup.on_import := None ;
  Thmod.reset () ;
  D.Setup.mode := `interactive ;
  D.Setup.file_kind := `thm ;
  D.Setup.annotate := true ;
  D.Setup.recurse := false ;
  D.Setup.import_mode := `auto ;
  D.Setup.trust_compiled := true ;
  D.Setup.compiled := None ;
  D.Setup.unfinished := [] ;
  D.Setup.input := "main.thm" ;
  Output.collect_mode () ;
  ignore (Output.drain ())

let with_session f =
  let thc_cache_limit = !Source.thc_cache_limit in
  let saved_processing_state = !processing_state in
  let cleanup () =
    Source.clear_virtual () ;
    Source.clear_thc_trust () ;
    Source.set_thc_cache_limit thc_cache_limit ;
    Accumulate.clear_specification_cache () ;
    processing_state := saved_processing_state
  in
  Fun.protect ~finally:cleanup (fun () ->
    D.Setup.with_saved (fun () ->
      start_thm_session () ;
      f ()))

let process_command command =
  let lb = Lexing.from_string command in
  lb.Lexing.lex_curr_p <- {
    lb.Lexing.lex_curr_p with
    Lexing.pos_fname = !D.Setup.input
  } ;
  D.Setup.lexbuf := lb ;
  let status =
    try
      match D.process1 !processing_state with
      | Ok state ->
          processing_state := state ;
          Ok ()
      | Error _ as status -> status
    with
    | D.Setup.AbellaExit 0 -> Ok ()
    | D.Setup.AbellaExit _ ->
        Error (D.Runtime_error "process aborted")
  in
  (status, Output.drain ())

let system_messages messages =
  List.filter_map begin function
    | `Assoc fields -> begin
        match List.assoc_opt "type" fields,
              List.assoc_opt "message" fields with
        | Some (`String "system_message"), Some (`String msg) -> Some msg
        | _ -> None
      end
    | _ -> None
  end messages

let error_messages messages =
  List.filter_map begin function
    | `Assoc fields -> begin
        match List.assoc_opt "severity" fields,
              List.assoc_opt "message" fields with
        | Some (`String "error"), Some (`String msg) -> Some msg
        | _ -> None
      end
    | _ -> None
  end messages

let assert_ok : ('a, 'b) Result.t -> unit = function
  | Ok _ -> ()
  | Error _ -> Alcotest.fail "command failed"

let assert_contains needle haystack =
  let found = List.exists begin fun text ->
      let n = String.length needle and h = String.length text in
      let rec spin i =
        i + n <= h && (String.sub text i n = needle || spin (i + 1))
      in
      spin 0
    end haystack
  in
  Alcotest.check Alcotest.bool
    ("expected message containing " ^ needle) true found

let read_thc_file path =
  let ch = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ch) begin fun () ->
    let digest = (Marshal.from_channel ch : Digest.t) in
    let version = (Marshal.from_channel ch : string) in
    let sign = (Marshal.from_channel ch : Typing.sign) in
    let clauses = (Marshal.from_channel ch : clause list) in
    let predicates = (Marshal.from_channel ch : string list) in
    let content = (Marshal.from_channel ch : compiled list) in
    ignore digest ; ignore version ;
    (sign, clauses, predicates, content)
  end

let run_thm dir name source =
  let path = Filename.concat dir (name ^ ".thm") in
  write_file path source ;
  State.reload D.initial_snapshot ;
  Thmod.reset () ;
  State.Undo.set_enabled false ;
  D.Setup.compiling := [] ;
  D.Setup.mode := `batch ;
  D.Setup.annotate := false ;
  D.Setup.recurse := false ;
  D.Setup.import_mode := `thc ;
  D.Setup.trust_compiled := false ;
  D.Setup.unfinished := [] ;
  D.Setup.file_kind := `thm ;
  D.Setup.input := path ;
  let module Src = (val Thm.read path) in
  D.Setup.compiled := Some (module Src) ;
  D.Setup.lexbuf := Src.lex true ;
  Output.collect_mode () ;
  ignore (Output.drain ()) ;
  let rec drive state =
    try
      match D.process1 state with
      | Ok state -> drive state
      | Error _ -> drive state
    with
    | D.Setup.AbellaExit 0 -> ()
    | D.Setup.AbellaExit n -> raise (D.Setup.AbellaExit n)
  in
  try
    drive D.Process_top ;
    `Ok (read_file Src.thc_path)
  with
  | D.Setup.AbellaExit _ -> `Error (Output.collected_messages ())
  | e -> `Error (Printexc.to_string e)

let native_compile_thm dir name source =
  match run_thm dir name source with
  | `Ok bytes -> bytes
  | `Error msg -> Alcotest.fail msg

let expect_thm_error dir name source needle =
  match run_thm dir name source with
  | `Ok _ -> Alcotest.fail ("expected an error containing " ^ needle)
  | `Error msg ->
      Alcotest.check Alcotest.bool
        ("expected error containing " ^ needle) true
        (let n = String.length needle in
         let rec spin i =
           i + n <= String.length msg &&
           (String.sub msg i n = needle || spin (i + 1))
         in
         spin 0)

let run_thmod dir name source =
  let path = Filename.concat dir (name ^ ".thmod") in
  write_file path source ;
  State.reload D.initial_snapshot ;
  Thmod.reset () ;
  State.Undo.set_enabled false ;
  D.Setup.compiling := [] ;
  D.Setup.mode := `batch ;
  D.Setup.annotate := false ;
  D.Setup.recurse := false ;
  D.Setup.import_mode := `thc ;
  D.Setup.trust_compiled := false ;
  D.Setup.unfinished := [] ;
  D.Setup.file_kind := `thmod ;
  D.Setup.input := path ;
  let module Src = (val Thmod.read path) in
  D.Setup.compiled := Some (module Src) ;
  D.Setup.lexbuf := Src.lex true ;
  Output.collect_mode () ;
  ignore (Output.drain ()) ;
  let rec drive state =
    try
      match D.process1 state with
      | Ok state -> drive state
      | Error _ -> drive state
    with
    | D.Setup.AbellaExit 0 -> ()
    | D.Setup.AbellaExit n -> raise (D.Setup.AbellaExit n)
  in
  try
    drive D.Process_top ;
    `Ok (read_file Src.thc_path)
  with
  | D.Setup.AbellaExit _ -> `Error (Output.collected_messages ())
  | e -> `Error (Printexc.to_string e)

let native_compile_thmod dir name source =
  match run_thmod dir name source with
  | `Ok bytes -> bytes
  | `Error msg -> Alcotest.fail msg

let thm_module = {|
Kind tm type.
Type app tm -> tm -> tm.

Define is_app : tm -> prop by
  is_app (app A B).

Theorem mod_ok : forall A B, is_app (app A B).
intros. search.
|}

let spec_sig = {|
sig spec.
kind tm type.
type app tm -> tm -> tm.
type copy tm -> tm -> o.
|}

let spec_mod = {|
module spec.
copy (app N M) (app P Q) :- copy N P, copy M Q.
|}

let test_read_thm_defaults () =
  with_session begin fun () ->
    Source.add_virtual "mods/Foo.thm" "Theorem t : true. intros. search." ;
    let module Src = (val Thm.read "mods/Foo.thm") in
    Alcotest.check Alcotest.string "path" "mods/Foo.thm" Src.path ;
    Alcotest.check Alcotest.string "output path"
      "mods/Foo.out" Src.out_path ;
    Alcotest.check Alcotest.string "artifact path"
      "mods/Foo.thc" Src.thc_path ;
    Alcotest.check Alcotest.bool "is stale" true Src.is_stale ;
    Source.add_virtual "mods/Foo.thc" "artifact" ;
    Source.set_thc_trusted "mods/Foo.thc" true ;
    let module Src = (val Thm.read "mods/Foo.thm") in
    Alcotest.check Alcotest.bool "is stale after trust" false Src.is_stale ;
    Alcotest.check Alcotest.string "artifact contents"
      "artifact" (Src.thc_contents ())
  end

let test_thm_artifact_layout () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      let bytes = native_compile_thm dir "layout" {|
Kind u type.
Type c u.
Type p u -> prop.
Define d : u -> prop by d X.
Theorem t : forall (x:u), d x.
intros. search.
Axiom ax : forall (x:u), d x.
|} in
      ignore bytes ;
      let (sign, clauses, predicates, content) =
        read_thc_file (Filename.concat dir "layout.thc") in
      Alcotest.check Alcotest.bool "no specification kinds" true
        (fst sign = []) ;
      Alcotest.check Alcotest.bool "no specification constants" true
        (snd sign = []) ;
      Alcotest.check Alcotest.bool "no specification clauses" true
        (clauses = []) ;
      Alcotest.check Alcotest.bool "predicate recorded" true
        (List.mem "d" predicates) ;
      let has pred = List.exists pred content in
      Alcotest.check Alcotest.bool "kind declaration" true
        (has (function CKind (["u"], _) -> true | _ -> false)) ;
      Alcotest.check Alcotest.bool "type declaration" true
        (has (function CType (["c"], _, _) -> true | _ -> false)) ;
      Alcotest.check Alcotest.bool "definition" true
        (has (function CDefine (_, _, [("d", _)], _) -> true | _ -> false)) ;
      Alcotest.check Alcotest.bool "finished theorem" true
        (has (function
             | CTheorem ("t", [], _, Finished) -> true
             | _ -> false)) ;
      Alcotest.check Alcotest.bool "axiom tag" true
        (has (function
             | CTheorem ("ax", [], _, Axiomatic) -> true
             | _ -> false))
    end
  end

let test_specification_state () =
  with_session begin fun () ->
    Source.add_virtual "spec.sig" spec_sig ;
    Source.add_virtual "spec.mod" spec_mod ;
    let (status, _) = process_command "Specification \"spec\"." in
    assert_ok status ;
    Alcotest.check Alcotest.bool "specification consumed" false
      !Thm.can_read_specification ;
    Alcotest.check Alcotest.bool "specification kind recorded" true
      (List.mem_assoc "tm" (fst !D.Setup.spec_sign)) ;
    Alcotest.check Alcotest.bool "specification clauses recorded" true
      (!D.Setup.spec_clauses <> []) ;
    let (status, msgs) = process_command "Specification \"spec\"." in
    Alcotest.check Alcotest.bool "second specification fails" true
      (Result.is_error status) ;
    assert_contains "Specification can only be read"
      (system_messages msgs)
  end

let test_specification_artifact () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      write_file (Filename.concat dir "spec.sig") spec_sig ;
      write_file (Filename.concat dir "spec.mod") spec_mod ;
      ignore (native_compile_thm dir "withspec" {|
Specification "spec".
Theorem t : true.
intros. search.
|}) ;
      let (sign, clauses, _, content) =
        read_thc_file (Filename.concat dir "withspec.thc") in
      Alcotest.check Alcotest.bool "specification kind in artifact" true
        (List.mem_assoc "tm" (fst sign)) ;
      Alcotest.check Alcotest.bool "specification clauses in artifact" true
        (clauses <> []) ;
      Alcotest.check Alcotest.bool "theorem after specification" true
        (List.exists (function
             | CTheorem ("t", [], _, Finished) -> true
             | _ -> false) content)
    end
  end

let test_specification_keyword_warning () =
  with_session begin fun () ->
    Source.add_virtual "kw.sig" {|
sig kw.
kind local type.
|} ;
    Source.add_virtual "kw.mod" "module kw.\n" ;
    let (status, msgs) = process_command "Specification \"kw\"." in
    assert_ok status ;
    assert_contains "keywords in Teyjus: local" (system_messages msgs)
  end

let test_source_import_cache () =
  with_session begin fun () ->
    Source.add_virtual "main.thm" "" ;
    Source.add_virtual "mod.thm" thm_module ;
    let hits = ref [] in
    D.Setup.on_import := Some (fun name -> hits := name :: !hits) ;
    let (status, msgs) = process_command "Import \"mod\"." in
    assert_ok status ;
    Alcotest.check Alcotest.bool "generated thc exists" true
      (Source.virtual_exists "mod.thc") ;
    Alcotest.check Alcotest.bool "generated thc trusted" true
      (Source.is_thc_trusted "mod.thc") ;
    Alcotest.check (Alcotest.list Alcotest.string)
      "string lists differ" ["mod"] !hits ;
    Alcotest.check (Alcotest.list Alcotest.string)
      "string lists differ" [] (error_messages msgs) ;

    (* Rewind over the import; the generated .thc stays in the virtual FS. *)
    assert_ok (try State.Undo.back 1 ; Ok () with Failure _ -> Error ()) ;
    hits := [] ;
    let (status, _) = process_command "Import \"mod\"." in
    assert_ok status ;
    Alcotest.check (Alcotest.list Alcotest.string)
      "string lists differ" [] !hits ;

    let (status, _) = process_command
        "Theorem root_ok : forall A B, is_app (app A B)." in
    assert_ok status ;
    assert_ok (fst (process_command "intros.")) ;
    let (status, msgs) = process_command "search." in
    assert_ok status ;
    assert_contains "Proof completed" (system_messages msgs) ;

    let (status, msgs) = process_command "Import \"nope\"." in
    Alcotest.check Alcotest.bool "missing import fails" true
      (Result.is_error status) ;
    assert_contains "Opening: ./nope.thm" (system_messages msgs)
  end

let test_import_source_mode () =
  with_session begin fun () ->
    Source.add_virtual "mod.thm" thm_module ;
    Source.add_virtual "mod.thc" "not a real artifact" ;
    Source.set_thc_trusted "mod.thc" true ;
    D.Setup.import_mode := `source ;
    let (status, _) = process_command "Import \"mod\"." in
    assert_ok status ;
    let generated = Source.virtual_contents "mod.thc" in
    Alcotest.check Alcotest.bool "compiled from source" true
      (generated <> "not a real artifact") ;
    Alcotest.check Alcotest.bool "generated thc trusted" true
      (Source.is_thc_trusted "mod.thc")
  end

let test_input_path_relative_imports () =
  with_session begin fun () ->
    Source.add_virtual "nested/main.thm" "" ;
    Source.add_virtual "nested/mod.thm" thm_module ;
    D.Setup.input := "nested/main.thm" ;
    let module Src = (val Thm.read "nested/main.thm") in
    Alcotest.check Alcotest.string "input path"
      "nested/main.thm" Src.path ;
    Filepath.set_load_path ~wrt:!D.Setup.input "lib" ;
    Alcotest.check Alcotest.string "load path"
      "nested/lib" !Filepath.load_path ;
    let (status, _) = process_command "Import \"mod\"." in
    assert_ok status ;
    Alcotest.check Alcotest.bool "nested thc" true
      (Source.virtual_exists "nested/mod.thc")
  end

let test_ctype_stores_typarams () =
  with_session begin fun () ->
    assert_ok (fst (process_command
      "Type decl_local A -> B -> prop.")) ;
    match !Thm.comp_content with
    | [CType(["decl_local"], typarams, _)] ->
        Alcotest.check (Alcotest.list Alcotest.string)
          "type parameters differ" ["A" ; "B"] typarams
    | _ -> Alcotest.fail "expected a CType declaration"
  end

let test_decl_pred_replay_preserves_typarams () =
  with_session begin fun () ->
    let a = tybase (Tygenvar "A") in
    let b = tybase (Tygenvar "B") in
    let pred_ty = tyarrow [a; b] propty in
    let const_ty = tyarrow [a] b in
    let repl = Thm.Replacement.make [] in
    Thm.process_decls ~repl ~modname:"test" [
      CDeclPred(["decl_pred"], ["A"], pred_ty) ;
      CType(["decl_const"], ["A"], const_ty) ;
    ] ;
    let check_scheme name expected ty =
      match List.assoc name (snd !Typing.sign) with
      | Poly(typarams, scheme_ty) ->
          Alcotest.check (Alcotest.list Alcotest.string)
            (name ^ " type parameters") expected typarams ;
          Alcotest.check ty_testable (name ^ " type") ty scheme_ty
      | exception Not_found ->
          Alcotest.fail ("missing declaration " ^ name)
    in
    check_scheme "decl_pred" ["A"] pred_ty ;
    check_scheme "decl_const" ["A"] const_ty
  end

let test_values_match_native () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      ignore (native_compile_thm dir "mod" thm_module) ;
      start_thm_session () ;
      Source.add_virtual "main.thm" "" ;
      Source.add_virtual "mod.thm" thm_module ;
      let (status, _) = process_command "Import \"mod\"." in
      assert_ok status ;
      let generated_path = Filename.concat dir "generated.thc" in
      write_file generated_path (Source.virtual_contents "mod.thc") ;
      let (ns, nc, np, nt) =
        read_thc_file (Filename.concat dir "mod.thc") in
      let (ws, wc, wp, wt) = read_thc_file generated_path in
      Alcotest.check Alcotest.bool "spec sign differs" true (ns = ws) ;
      Alcotest.check Alcotest.bool "spec clauses differ" true (nc = wc) ;
      Alcotest.check Alcotest.bool "predicates differ" true (np = wp) ;
      Alcotest.check Alcotest.bool "compiled content differs" true (nt = wt)
    end
  end

let test_virtual_native_thc () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      let native = native_compile_thm dir "mod" thm_module in
      start_thm_session () ;
      Source.add_virtual "main.thm" "" ;
      Source.add_virtual "mod.thm" thm_module ;
      Source.add_virtual "mod.thc" native ;
      Source.set_thc_trusted "mod.thc" true ;
      let hits = ref [] in
      D.Setup.on_import := Some (fun name -> hits := name :: !hits) ;
      let (status, _) = process_command "Import \"mod\"." in
      assert_ok status ;
      Alcotest.check (Alcotest.list Alcotest.string)
        "string lists differ" [] !hits ;
      let (status, _) = process_command
          "Theorem root_ok : forall A B, is_app (app A B)." in
      assert_ok status ;
      assert_ok (fst (process_command "intros.")) ;
      let (status, msgs) = process_command "search." in
      assert_ok status ;
      assert_contains "Proof completed" (system_messages msgs)
    end
  end

let test_nested_imports () =
  with_session begin fun () ->
    Source.add_virtual "main.thm" "" ;
    Source.add_virtual "inner.thm" {|
Kind tm type.
Type app tm -> tm -> tm.
Define is_inner : tm -> prop by is_inner (app A B).
|} ;
    Source.add_virtual "outer.thm" {|
Import "inner".
Theorem outer_ok : forall A B, is_inner (app A B).
intros. search.
|} ;
    let hits = ref [] in
    D.Setup.on_import := Some (fun name -> hits := name :: !hits) ;
    assert_ok (fst (process_command "Import \"outer\".")) ;
    Alcotest.check Alcotest.bool "inner thc" true
      (Source.is_thc_trusted "inner.thc") ;
    Alcotest.check Alcotest.bool "outer thc" true
      (Source.is_thc_trusted "outer.thc") ;
    Alcotest.check (Alcotest.list Alcotest.string)
      "string lists differ" ["inner" ; "outer"] !hits
  end

let test_import_with_capture_avoidance () =
  with_session begin fun () ->
    Source.add_virtual "main.thm" "" ;
    Source.add_virtual "withmod.thm" {|
Kind nat type.
Type p nat -> prop.
Axiom foo : forall q, p q.
|} ;
    assert_ok (fst (process_command "Kind nat type.")) ;
    assert_ok (fst (process_command "Type p, q nat -> prop.")) ;
    let (status, _) = process_command
        "Import \"withmod\" with p := q." in
    assert_ok status ;
    let (_, thm) = Prover.get_generic_lemma "foo" in
    Alcotest.check Alcotest.string "imported theorem captured"
      "forall q1, q q1" (Metaterm.metaterm_to_string thm)
  end

let test_error_locations_use_input_path () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      let path = Filename.concat dir "Location.thm" in
      expect_thm_error dir "Location" {|
Kind u type.
Type c u.
Theorem bad : true.
nonsense.
|} path
    end
  end

let test_import_requires_distinct_replacements () =
  with_session begin fun () ->
    Source.add_virtual "main.thm" "" ;
    Source.add_virtual "dup.thm" "Type p, q prop." ;
    assert_ok (fst (process_command "Type r prop.")) ;
    let (status, msgs) =
      process_command "Import \"dup\" with p := r, q := r." in
    Alcotest.check Alcotest.bool "duplicate replacements fail" true
      (Result.is_error status) ;
    assert_contains "not pairwise" (system_messages msgs)
  end

let test_import_replacements_are_simultaneous () =
  with_session begin fun () ->
    Source.add_virtual "main.thm" "" ;
    Source.add_virtual "swap.thm" "Type p, q prop." ;
    assert_ok (fst (process_command "Type p, q prop.")) ;
    let (status, msgs) =
      process_command "Import \"swap\" with p := q, q := p." in
    assert_ok status ;
    Alcotest.check (Alcotest.list Alcotest.string)
      "string lists differ" [] (error_messages msgs)
  end

let test_split_propagates_tags () =
  with_session begin fun () ->
    Source.add_virtual "skipmod.thm" {|
Theorem imported_skip : true /\ true.
skip.
|} ;
    let check_tag expected name =
      Alcotest.check Alcotest.bool (name ^ " tag differs") true
        (Prover.get_lemma_tag name = expected)
    in
    let check_names message expected names =
      Alcotest.check (Alcotest.list Alcotest.string) message
        (List.sort compare expected) (List.sort compare names)
    in
    assert_ok (fst (process_command "Axiom ax : true /\\ true.")) ;
    assert_ok (fst (process_command "Split ax as ax1, ax2.")) ;
    List.iter (check_tag Axiomatic) ["ax" ; "ax1" ; "ax2"] ;
    check_names "axioms differ" ["ax"] !D.Setup.axioms ;
    assert_ok (fst (process_command "Theorem skipped : true /\\ true.")) ;
    assert_ok (fst (process_command "skip.")) ;
    assert_ok (fst (process_command "Split skipped as sk1, sk2.")) ;
    List.iter (check_tag Unfinished) ["skipped" ; "sk1" ; "sk2"] ;
    check_names "unfinished differ" ["skipped" ; "sk1" ; "sk2"]
      !D.Setup.unfinished ;
    assert_ok (fst (process_command "Import \"skipmod\".")) ;
    assert_ok (fst (process_command "Split imported_skip as is1, is2.")) ;
    List.iter (check_tag Unfinished)
      ["imported_skip" ; "is1" ; "is2"] ;
    check_names "imported unfinished reported" ["skipped" ; "sk1" ; "sk2"]
      !D.Setup.unfinished ;
    assert_ok (fst (process_command "Theorem done : true /\\ true.")) ;
    assert_ok (fst (process_command "split.")) ;
    assert_ok (fst (process_command "search.")) ;
    assert_ok (fst (process_command "search.")) ;
    assert_ok (fst (process_command "Split done as done1, done2.")) ;
    List.iter (check_tag Finished) ["done" ; "done1" ; "done2"] ;
    check_names "unfinished changed" ["skipped" ; "sk1" ; "sk2"]
      !D.Setup.unfinished ;
    check_names "axioms changed" ["ax"] !D.Setup.axioms
  end

let test_import_cycle () =
  with_session begin fun () ->
    Source.add_virtual "main.thm" "" ;
    Source.add_virtual "a.thm" "Import \"b\"." ;
    Source.add_virtual "b.thm" "Import \"a\"." ;
    let (status, msgs) = process_command "Import \"a\"." in
    Alcotest.check Alcotest.bool "cycle fails" true
      (Result.is_error status) ;
    assert_contains "Cyclic import" (system_messages msgs)
  end

let test_module_already_imported () =
  with_session begin fun () ->
    assert_ok (fst (process_command "Module X.")) ;
    assert_ok (fst (process_command "Kind u type.")) ;
    assert_ok (fst (process_command "End X.")) ;
    assert_ok (fst (process_command "Import Module M = X.")) ;
    let (status, msgs) = process_command "Module M." in
    Alcotest.check Alcotest.bool "conflicting module fails" true
      (Result.is_error status) ;
    assert_contains "Module name M is already imported"
      (system_messages msgs)
  end

let test_inline_module () =
  with_session begin fun () ->
    assert_ok (fst (process_command "Module M.")) ;
    assert_ok (fst (process_command "Kind u type.")) ;
    assert_ok (fst (process_command "Type c u.")) ;
    assert_ok (fst (process_command "Define p : u -> prop by p X.")) ;
    assert_ok (fst (process_command "End M.")) ;
    assert_ok (fst (process_command "Import Module I = M.")) ;
    assert_ok (fst (process_command "Type d I.u.")) ;
    assert_ok (fst (process_command "Theorem t : I.p d.")) ;
    assert_ok (fst (process_command "intros.")) ;
    assert_ok (fst (process_command "search.")) ;
    ignore (Prover.get_generic_lemma "t")
  end

let test_inline_thm_modules () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      ignore (native_compile_thm dir "OnlyModule" {|
Module M.
  Kind u type.
  Type c u.
End M.
|}) ;
      let (_, _, _, content) =
        read_thc_file (Filename.concat dir "OnlyModule.thc") in
      Alcotest.check Alcotest.int "module definitions are not persisted"
        0 (List.length content) ;
      ignore (native_compile_thm dir "UseModule" {|
Module M.
  Kind u type.
  Type c u.
  Define p : u -> prop by
    p X.
End M.
Import Module I = M.
Type d I.u.
Theorem t : I.p d.
intros. search.
|}) ;
      let (_, _, _, content) =
        read_thc_file (Filename.concat dir "UseModule.thc") in
      let has_kind =
        List.exists (function CKind (["I.u"], _) -> true | _ -> false)
          content
      in
      let has_type =
        List.exists (function CType (["d"], _, _) -> true | _ -> false)
          content
      in
      let has_thm =
        List.exists (function
            | CTheorem ("t", [], _, Finished) -> true
            | _ -> false) content
      in
      Alcotest.check Alcotest.bool "imported internal kind" true has_kind ;
      Alcotest.check Alcotest.bool "declaration over imported kind" true
        has_type ;
      Alcotest.check Alcotest.bool "theorem over imported definition" true
        has_thm ;
      ignore (native_compile_thm dir "NestedInline" {|
Module Outer.
  Module Inner.
    Kind u type.
    Type c u.
    Define p : u -> prop by
      p X.
  End Inner.
  Import Module I = Inner.
  Type d I.u.
  Theorem t : I.p d.
  intros. search.
End Outer.
Import Module O = Outer.
Type e O.I.u.
Theorem u : O.I.p e.
intros. search.
|}) ;
      let (_, _, _, content) =
        read_thc_file (Filename.concat dir "NestedInline.thc") in
      let has_nested_kind =
        List.exists (function CKind (["O.I.u"], _) -> true | _ -> false)
          content
      in
      let has_nested_type =
        List.exists (function CType (["e"], _, _) -> true | _ -> false)
          content
      in
      Alcotest.check Alcotest.bool "nested internal kind" true
        has_nested_kind ;
      Alcotest.check Alcotest.bool "use of nested internal kind" true
        has_nested_type ;
      ignore (native_compile_thm dir "SeqInline" {|
Module SeqInline.
  Theorem t : forall (x:o), { x |- x }.
  intros. search.
End SeqInline.
|})
    end
  end

let test_inline_thm_errors () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      expect_thm_error dir "BadImport" {|
Module BadImport.
  Kind u type.
  Type c u.
  Import "x".
End BadImport.
|} "A module may not use ordinary Import" ;
      expect_thm_error dir "BadSpec" {|
Module BadSpec.
  Specification "x".
End BadSpec.
|} "Specification is not allowed in a module" ;
      expect_thm_error dir "BadClose" {|
Module BadClose.
  Kind u type.
  Close u.
End BadClose.
|} "Close is not allowed in a module" ;
      expect_thm_error dir "BadSuspend" {|
Module BadSuspend.
  Suspend p X.
End BadSuspend.
|} "Suspend is not allowed in a module" ;
      expect_thm_error dir "BadQuit" {|
Module BadQuit.
  Quit.
End BadQuit.
|} "Quit is not allowed in a module" ;
      expect_thm_error dir "DuplicateModule" {|
Module DuplicateModule.
End DuplicateModule.
Module DuplicateModule.
End DuplicateModule.
|} "already declared" ;
      expect_thm_error dir "BadEnd" {|
Module BadEnd.
End OtherEnd.
|} "does not match Module"
    end
  end

let test_import_thm_flattening () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      ignore (native_compile_thmod dir "Box4" {|
Module Box4[T].
  Type p T -> prop.
End Box4.
|}) ;
      begin match run_thm dir "b" {|
Kind w type.
Type cw w.
Import Module B = "Box4"[w].
Theorem bt : B.p cw -> B.p cw.
intros. search.
|} with
      | `Ok _ -> ()
      | `Error msg -> Alcotest.fail msg
      end ;
      begin match run_thm dir "c" {|
Import "b".
Theorem ct : B.p cw -> B.p cw.
intros. search.
|} with
      | `Ok _ -> ()
      | `Error msg -> Alcotest.fail msg
      end
    end
  end

let tests = suite "thm" [
    test_case "read thm defaults" test_read_thm_defaults ;
    test_case "artifact layout" test_thm_artifact_layout ;
    test_case "specification state" test_specification_state ;
    test_case "specification artifact" test_specification_artifact ;
    test_case "specification keyword warning"
      test_specification_keyword_warning ;
    test_case "source import cache" test_source_import_cache ;
    test_case "import source mode" test_import_source_mode ;
    test_case "input path relative imports"
      test_input_path_relative_imports ;
    test_case "ctype stores typarams" test_ctype_stores_typarams ;
    test_case "decl pred replay preserves typarams"
      test_decl_pred_replay_preserves_typarams ;
    test_case "values match native" test_values_match_native ;
    test_case "virtual native thc" test_virtual_native_thc ;
    test_case "nested imports" test_nested_imports ;
    test_case "import with capture avoidance"
      test_import_with_capture_avoidance ;
    test_case "error locations use input path"
      test_error_locations_use_input_path ;
    test_case "import requires distinct replacements"
      test_import_requires_distinct_replacements ;
    test_case "import replacements are simultaneous"
      test_import_replacements_are_simultaneous ;
    test_case "split propagates tags" test_split_propagates_tags ;
    test_case "import cycle" test_import_cycle ;
    test_case "module already imported" test_module_already_imported ;
    test_case "inline module" test_inline_module ;
    test_case "inline thm modules" test_inline_thm_modules ;
    test_case "inline thm errors" test_inline_thm_errors ;
    test_case "import thm flattening" test_import_thm_flattening ;
  ]
