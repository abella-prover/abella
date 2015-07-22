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

let re_init =
  let reset_snap = State.snapshot () in
  fun () -> State.reload reset_snap

class type run_result = object
  method status : Js.js_string Js.t Js.writeonly_prop
  method output : Js.js_string Js.t Js.writeonly_prop
end

exception ProcessFailure

let capture_everything fn : run_result Js.t =
  let buf = Buffer.create 19 in
  Checks.out := Format.formatter_of_buffer buf ;
  Checks.err := !Checks.out ;
  Extensions.really_exit := false ;
  let status = ref "good" in
  begin try fn () with
  | Exit n ->
      status := (if n = 0 then "good" else "bad")
  | ProcessFailure ->
      status := "bad"
  | e ->
      let msg = match e with
        | Failure msg -> msg
        | _ -> Printexc.to_string e
      in
      Format.fprintf !Checks.out "Error: %s@." msg ;
      status := "bad"
  end ;
  let return : run_result Js.t = Js.Unsafe.obj [| |] in
  return##status <- Js.string !status ;
  Format.pp_print_flush !Checks.out () ;
  return##output <- Js.string (Buffer.contents buf) ;
  return

let abella_batch spec_sig spec_mod thm =
  re_init () ;
  capture_everything begin fun () ->
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
    Abella_driver.main () ;
  end

let abella_process1 directive =
  capture_everything begin fun () ->
    let directive = Js.to_string directive in
    Abella_driver.lexbuf := Lexing.from_string directive ;
    Abella_driver.unprompt () ; (* suppress prompt *)
    Format.fprintf !Checks.out "%s@." directive ;
    let status = Abella_driver.process1 () in (* actual *)
    Abella_driver.process1 () |> ignore ;     (* get next prompt *)
    if status = Abella_driver.FAILURE then raise ProcessFailure
  end

let abella_reset spec_sig spec_mod =
  capture_everything begin fun () ->
    let spec_sig = Js.to_string spec_sig in
    let sig_name = get_name sig_regexp "signature" spec_sig in
    let spec_mod = Js.to_string spec_mod in
    let mod_name = get_name mod_regexp "module" spec_mod in
    if sig_name <> mod_name then
      failwithf "Names of signature (%S) and module (%S) do not agree.\nCheck your Specification."
        sig_name mod_name ;
    File_cache.reset () ;
    File_cache.add ("./" ^ sig_name ^ ".sig") spec_sig ;
    File_cache.add ("./" ^ mod_name ^ ".mod") spec_mod ;
    Format.fprintf !Checks.out "%s%!" Abella_driver.welcome_msg ;
    Abella_driver.process1 () |> ignore ; (* initial prompt *)
  end

class type abella_js = object
  method batch : (Js.js_string Js.t -> Js.js_string Js.t -> Js.js_string Js.t -> run_result Js.t) Js.callback Js.writeonly_prop
  method reset : (Js.js_string Js.t -> Js.js_string Js.t -> run_result Js.t) Js.callback Js.writeonly_prop
  method process1 : (Js.js_string Js.t -> run_result Js.t) Js.callback Js.writeonly_prop
end

let make_abella_js () =
  let abella_js : abella_js Js.t = Js.Unsafe.obj [| |] in
  abella_js##batch    <- Js.wrap_callback abella_batch ;
  abella_js##reset    <- Js.wrap_callback abella_reset ;
  abella_js##process1 <- Js.wrap_callback abella_process1 ;
  abella_js

let () =
  Js.Unsafe.global##abella <- make_abella_js ()
  (* Js.Unsafe.set Js.Unsafe.global "run_abella" (Js.wrap_callback abella_batch) *)
