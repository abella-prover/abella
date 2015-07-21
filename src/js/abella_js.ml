(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions

let sig_regexp = Regexp.regexp "sig\\s+([^\\s]+)\\."
let mod_regexp = Regexp.regexp "module\\s+([^\\s]+)\\."

let get_name re kind text =
  match Regexp.string_match re text 0 with
  | None -> failwithf "Could not determing %s name" kind
  | Some res -> Option.default "unknown-spec" (Regexp.matched_group res 1)

class type run_result = object
  method status : Js.js_string Js.t Js.writeonly_prop
  method output : Js.js_string Js.t Js.writeonly_prop
end

let run_abella_internal spec_sig spec_mod thm =
  let buf = Buffer.create 19 in
  Checks.out := Format.formatter_of_buffer buf ;
  Checks.err := !Checks.out ;
  Extensions.really_exit := false ;
  let snap = State.snapshot () in
  let status = ref "good" in
  begin try
    let spec_sig = Js.to_string spec_sig in
    let sig_name = get_name sig_regexp "signature" spec_sig in
    let spec_mod = Js.to_string spec_mod in
    let mod_name = get_name mod_regexp "module" spec_mod in
    if sig_name <> mod_name then
      failwithf "Names of signature (%S) and module (%S) do not agree.\nCheck your Specification."
        sig_name mod_name ;
    let thm = Js.to_string thm in
    File_cache.reset () ;
    File_cache.add ("./" ^ sig_name ^ ".sig") spec_sig ;
    File_cache.add ("./" ^ mod_name ^ ".mod") spec_mod ;
    File_cache.add "reasoning.thm" thm ;
    Abella_driver.input_files := ["reasoning.thm"] ;
    State.Undo.reset () ;
    Abella_driver.main ()
  with
  | Exit n ->
      status := (if n = 0 then "good" else "bad")
  | e ->
      let msg = match e with
        | Failure msg -> msg
        | _ -> Printexc.to_string e
      in
      Format.fprintf !Checks.out "Error: %s@." msg ;
      status := "bad"
  end ;
  State.reload snap ;
  let return : run_result Js.t = Js.Unsafe.obj [| |] in
  return##status <- Js.string !status ;
  return##output <- Js.string (Buffer.contents buf) ;
  return

let () =
  Js.Unsafe.set Js.Unsafe.global "run_abella" (Js.wrap_callback run_abella_internal)
