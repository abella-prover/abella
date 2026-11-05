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

(* Dependency extraction tests for .thm and .thmod sources. *)

open Abella_lib
open Extensions
open Test_helper

let write_file path contents =
  let ch = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out ch) (fun () ->
      output_string ch contents)

let with_temp_dir f =
  let dir = Filename.temp_file "abella-depend-test" "" in
  Sys.remove dir ;
  Unix.mkdir dir 0o700 ;
  Fun.protect ~finally:(fun () ->
      Array.iter (fun name -> Sys.remove (Filename.concat dir name))
        (Sys.readdir dir) ;
      Unix.rmdir dir)
    (fun () -> f dir)

let test_thm_dependencies () =
  with_temp_dir begin fun dir ->
    let base = Filename.concat dir "main" in
    write_file (base ^ ".thm") {|
Import "Lib".
Import Module "Box"[nat] with p := q.
Show Module "Shown".
|} ;
    let deps = Depend.file_dependencies `thm base in
    Alcotest.check (Alcotest.list Alcotest.string) "thm deps"
      [Filename.concat dir "Lib"] deps.Depend.dep_thms ;
    Alcotest.check (Alcotest.list Alcotest.string) "thmod deps"
      [Filename.concat dir "Box" ; Filename.concat dir "Shown"]
      deps.Depend.dep_thmods
  end

let test_thmod_dependencies () =
  with_temp_dir begin fun dir ->
    let base = Filename.concat dir "Main" in
    write_file (base ^ ".thmod") {|
Module Main.
  Import Module "Box".
  Import Module Local.
End Main.
|} ;
    let deps = Depend.file_dependencies `thmod base in
    Alcotest.check (Alcotest.list Alcotest.string) "thm deps" []
      deps.Depend.dep_thms ;
    Alcotest.check (Alcotest.list Alcotest.string) "thmod deps"
      [Filename.concat dir "Box"] deps.Depend.dep_thmods
  end

let tests = suite "Depend" [
    test_case "thm dependencies" test_thm_dependencies ;
    test_case "thmod dependencies" test_thmod_dependencies ;
  ]
