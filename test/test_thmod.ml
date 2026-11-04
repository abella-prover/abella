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

(* Tests for reasoning-level module files and artifacts. *)

open Abella_lib
open Abella_types
open Extensions
open Test_helper

module D = Abella_driver

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
  let dir = Filename.temp_file "abella-thmod-test" "" in
  Sys.remove dir ;
  Unix.mkdir dir 0o700 ;
  Fun.protect ~finally:(fun () -> remove_tree dir) (fun () -> f dir)

let with_session f =
  let snap = State.snapshot () in
  let dest = !Output.dest in
  let clause_map = !Typing.clause_map in
  let compiling = !D.compiling in
  let mode = !D.Setup.mode in
  let annotate = !D.Setup.annotate in
  let recurse = !D.Setup.recurse in
  let input = !D.Setup.input in
  let lexbuf = !D.Setup.lexbuf in
  let compiled = !D.Setup.compiled in
  let unfinished = !D.Setup.unfinished in
  let import_mode = !D.Setup.import_mode in
  let trust_compiled = !D.Setup.trust_compiled in
  let file_kind = !D.Setup.file_kind in
  let restore () =
    State.reload snap ;
    Output.dest := dest ;
    Typing.clause_map := clause_map ;
    D.compiling := compiling ;
    D.Setup.mode := mode ;
    D.Setup.annotate := annotate ;
    D.Setup.recurse := recurse ;
    D.Setup.input := input ;
    D.Setup.lexbuf := lexbuf ;
    D.Setup.compiled := compiled ;
    D.Setup.unfinished := unfinished ;
    D.Setup.import_mode := import_mode ;
    D.Setup.trust_compiled := trust_compiled ;
    D.Setup.file_kind := file_kind ;
    Source.clear_virtual () ;
    Source.clear_thc_trust () ;
    Accumulate.clear_specification_cache ()
  in
  Fun.protect ~finally:restore f

(* Compile [source] as a .thmod file named [name].thmod and return the
   bytes written to [name.thmodc]. *)
let native_compile_thmod dir name source =
  let path = Filename.concat dir (name ^ ".thmod") in
  write_file path source ;
  State.reload D.initial_snapshot ;
  State.Undo.set_enabled false ;
  D.compiling := [] ;
  D.Setup.mode := `batch ;
  D.Setup.annotate := false ;
  D.Setup.recurse := false ;
  D.Setup.import_mode := `thc ;
  D.Setup.trust_compiled := false ;
  D.Setup.unfinished := [] ;
  D.Setup.file_kind := `thmod ;
  D.Setup.input := path ;
  let module Src = (val Source.read_thmod path) in
  D.Setup.compiled := Some (module Src) ;
  D.Setup.lexbuf := Src.lex true ;
  Output.collect_mode () ;
  ignore (Output.drain ()) ;
  let rec drive () =
    try ignore (D.process1 ()) ; drive () with
    | D.AbellaExit 0 -> ()
    | D.AbellaExit n ->
        Alcotest.fail ("thmod compile exited " ^ string_of_int n)
  in
  drive () ;
  read_file Src.thc_path

let read_thmod_values bytes =
  let buf = Bytes.unsafe_of_string bytes in
  let pos = ref 0 in
  let read () =
    let v = Marshal.from_string bytes !pos in
    pos := !pos + Marshal.total_size buf !pos ;
    v
  in
  ignore (read () : Digest.t) ;
  ignore (read () : string) ;
  let name = (read () : string) in
  let params = (read () : string list) in
  ignore (read () : Typing.sign) ;
  ignore (read () : clause list) ;
  ignore (read () : string list) ;
  let content = (read () : compiled list) in
  let nested = (read () : string list) in
  let exports = (read () : string list) in
  (name, params, content, nested, exports)

let test_read_thmod_defaults () =
  with_session begin fun () ->
    Source.clear_virtual () ;
    Source.clear_thc_trust () ;
    Source.add_virtual "mods/Foo.thmod" "Module Foo.\nEnd Foo.\n" ;
    let module Src = (val Source.read_thmod "mods/Foo.thmod") in
    Alcotest.check Alcotest.string "path" "mods/Foo.thmod" Src.path ;
    Alcotest.check Alcotest.string "artifact path"
      "mods/Foo.thmodc" Src.thc_path ;
    Alcotest.check Alcotest.bool "is stale" true Src.is_stale ;
    Source.add_virtual "mods/Foo.thmodc" "artifact" ;
    Source.set_thc_trusted "mods/Foo.thmodc" true ;
    let module Src = (val Source.read_thmod "mods/Foo.thmod") in
    Alcotest.check Alcotest.bool "is stale after trust" false Src.is_stale ;
    Alcotest.check Alcotest.string "artifact contents"
      "artifact" (Src.thc_contents ())
  end

let test_thmod_artifact_layout () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      let bytes = native_compile_thmod dir "Foo" {|
Module Foo.
  Kind u type.
  Type c u.
  Type p u -> prop.
  Theorem refl : forall (x:u), x = x.
  intros. search.
End Foo.
|} in
      let (name, params, content, nested, exports) =
        read_thmod_values bytes
      in
      Alcotest.check Alcotest.string "module name" "Foo" name ;
      Alcotest.check (Alcotest.list Alcotest.string) "parameters"
        [] params ;
      Alcotest.check (Alcotest.list Alcotest.string) "nested modules"
        [] nested ;
      Alcotest.check (Alcotest.list Alcotest.string) "exports"
        [] exports ;
      let has_decl_pred =
        List.exists begin function
          | CDeclPred (["p"], [], _) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "declared predicate uses CDeclPred"
        true has_decl_pred ;
      let has_plain_type =
        List.exists begin function
          | CType (["c"], [], _) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "ordinary type uses CType"
        true has_plain_type ;
      let has_theorem =
        List.exists begin function
          | CTheorem ("refl", [], _, Finished) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "theorem is recorded" true has_theorem
    end
  end

let test_thmod_parameters_are_recorded () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      let bytes = native_compile_thmod dir "Foo" {|
Module Foo[T].
  Type p T -> prop.
End Foo.
|} in
      let (name, params, content, _, _) = read_thmod_values bytes in
      Alcotest.check Alcotest.string "module name" "Foo" name ;
      Alcotest.check (Alcotest.list Alcotest.string) "parameters"
        ["T"] params ;
      let has_decl_pred =
        List.exists begin function
          | CDeclPred (["p"], ["T"], _) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "declared predicate uses CDeclPred"
        true has_decl_pred
    end
  end

let tests =
  suite "thmod" [
      test_case "read_thmod defaults" test_read_thmod_defaults ;
      test_case "artifact layout" test_thmod_artifact_layout ;
      test_case "parameters are recorded" test_thmod_parameters_are_recorded ;
    ]
