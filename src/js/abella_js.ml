(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

let run_abella_internal spec_sig spec_mod thm =
  let spec_sig = "sig spec.\n" ^ Js.to_string spec_sig in
  let spec_mod = "module spec.\n" ^ Js.to_string spec_mod in
  let thm = "Specification \"spec\".\n" ^ Js.to_string thm in
  File_cache.reset () ;
  File_cache.add "./spec.sig" spec_sig ;
  File_cache.add "./spec.mod" spec_mod ;
  File_cache.add "reasoning.thm" thm ;
  Abella_driver.input_files := ["reasoning.thm"] ;
  let snap = State.snapshot () in
  State.Undo.reset () ;
  let buf = Buffer.create 19 in
  Checks.out := Format.formatter_of_buffer buf ;
  (try Abella_driver.main () with _ -> ()) ;
  State.reload snap ;
  Format.pp_print_flush !Checks.out () ;
  Buffer.contents buf |> Js.string

let () =
  Js.Unsafe.set Js.Unsafe.global "run_abella" (Js.wrap_callback run_abella_internal)
