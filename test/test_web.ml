(****************************************************************************)
(* Copyright (C) 2013-2026 Inria (Institut National de Recherche            *)
(*                                en Informatique et en Automatique)        *)
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

(* Tests for the browser-facing core: virtual sources, collected output,
   the generated .thc cache, and shared driver commands. *)

open Abella_lib
open Extensions
open Test_helper

module D = Abella_driver

let processing_state = ref D.Process_top

let start_web_session () =
  State.reload D.initial_snapshot ;
  processing_state := D.Process_top ;
  State.Undo.set_enabled true ;
  State.Undo.reset () ;
  Accumulate.clear_specification_cache () ;
  Source.clear_virtual () ;
  Source.clear_thc_trust () ;
  D.Setup.compiling := [] ;
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

(* Save and restore everything a prover session touches, so these tests
   do not disturb the rest of the suite. *)
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
      start_web_session () ;
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

let messages_of_type kind messages =
  List.filter_map begin function
    | `Assoc fields -> begin
        match List.assoc_opt "type" fields with
        | Some (`String k) when k = kind -> Some fields
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
  Alcotest.check Alcotest.bool ("expected message containing " ^ needle) true found

let test_virtual_source () =
  Alcotest.check Alcotest.bool "canon strip ./" true (Source.canon "./a/b.thm" = "a/b.thm") ;
  Alcotest.check Alcotest.bool "canon collapse dot" true (Source.canon "a/./b.thm" = "a/b.thm") ;
  Alcotest.check Alcotest.bool "canon collapse dotdot" true (Source.canon "a/x/../b.thm" = "a/b.thm") ;
  Source.add_virtual "./a/b.thm" "contents" ;
  Alcotest.check Alcotest.bool "virtual exists" true (Source.virtual_exists "a/b.thm") ;
  Alcotest.check Alcotest.string "strings differ" "contents" (Source.virtual_contents "a/b.thm") ;
  let module Src = (val Source.read "a/b.thm") in
  Alcotest.check Alcotest.string "strings differ" "a/b.thm" Src.path ;
  Alcotest.check (Alcotest.option Alcotest.string) "dir" (Some "a") Src.dir ;
  Alcotest.check (Alcotest.float 1e-9) "mtime" 0. Src.mtime ;
  let lb = Src.lex true in
  Alcotest.check Alcotest.string "strings differ" "a/b.thm" lb.Lexing.lex_curr_p.Lexing.pos_fname ;
  Alcotest.check Alcotest.bool "missing file" true begin
    try ignore (Source.read "nope.thm") ; false with Failure _ -> true
  end ;
  let bytes = "\000\001\255\254thc" in
  Source.add_virtual "gen/binary.thc" bytes ;
  Alcotest.check Alcotest.string "strings differ" bytes (Source.virtual_contents "gen/binary.thc") ;
  Source.clear_virtual () ;
  Alcotest.check Alcotest.bool "cleared" true (not (Source.virtual_exists "a/b.thm"))

let test_thc_cache_bound () =
  Source.set_thc_cache_limit 10 ;
  Source.add_virtual_thc "a.thc" "12345" ;
  Source.set_thc_trusted "a.thc" true ;
  Source.add_virtual_thc "b.thc" "12345" ;
  Alcotest.check Alcotest.int "ints differ" 10 (Source.thc_cache_size ()) ;
  Source.add_virtual_thc "c.thc" "12345" ;
  Alcotest.check Alcotest.bool "oldest thc evicted" true (not (Source.virtual_exists "a.thc")) ;
  Alcotest.check Alcotest.bool "evicted thc trust removed" true
    (not (Source.is_thc_trusted "a.thc")) ;
  Alcotest.check Alcotest.bool "newest thc kept" true (Source.virtual_exists "c.thc") ;
  Alcotest.check Alcotest.int "ints differ" 10 (Source.thc_cache_size ()) ;
  Source.clear_virtual () ;
  Source.set_thc_cache_limit 0 ;
  Source.add_virtual_thc "large.thc" (String.make 100 'x') ;
  Alcotest.check Alcotest.bool "unlimited keeps large thc" true (Source.virtual_exists "large.thc") ;
  Alcotest.check Alcotest.int "ints differ" 100 (Source.thc_cache_size ()) ;
  Source.add_virtual_thc "large.thc" "tiny" ;
  Alcotest.check Alcotest.int "ints differ" 4 (Source.thc_cache_size ()) ;
  Source.clear_virtual () ;
  Alcotest.check Alcotest.int "ints differ" 0 (Source.thc_cache_size ())

let test_output_collect () =
  Output.collect_mode () ;
  ignore (Output.drain ()) ;
  Output.msg_printf "one" ;
  Output.msg_printf ~severity:Error "two" ;
  let msgs = Output.drain () in
  Alcotest.check Alcotest.int "ints differ" 2 (List.length msgs) ;
  let texts = system_messages msgs in
  Alcotest.check (Alcotest.list Alcotest.string) "string lists differ" ["one" ; "two"] texts ;
  let severities = List.filter_map begin function
      | `Assoc fields -> begin
          match List.assoc_opt "severity" fields with
          | Some (`String s) -> Some s
          | _ -> None
        end
      | _ -> None
    end msgs in
  Alcotest.check (Alcotest.list Alcotest.string) "string lists differ" ["info" ; "error"] severities ;
  Alcotest.check Alcotest.int "ints differ" 0 (List.length (Output.drain ()))

let test_theorem_state () =
  let (status, msgs) = process_command "Theorem t : true." in
  assert_ok status ;
  let states = messages_of_type "theorem_state" msgs in
  Alcotest.check Alcotest.int "one theorem state" 1 (List.length states) ;
  let fields = List.hd states in
  let state =
    match List.assoc_opt "state" fields with
    | Some (`Assoc fields) -> fields
    | _ -> failwith "missing theorem state"
  in
  let goal =
    match List.assoc_opt "goal" state with
    | Some (`String goal) -> goal
    | _ -> failwith "missing theorem goal"
  in
  Alcotest.check Alcotest.string "initial goal" "true" goal ;
  start_web_session () ;
  let (status, msgs) = process_command "Axiom ax : true." in
  assert_ok status ;
  Alcotest.check Alcotest.int "axiom has no theorem state" 0
    (List.length (messages_of_type "theorem_state" msgs))

let has_kind name =
  List.exists (fun (id, _) -> id = name) (fst !Typing.sign)

let test_undo_back_counts () =
  let process_three prefix =
    let names = List.map (fun s -> prefix ^ s) ["a" ; "b" ; "c"] in
    List.iter (fun name ->
        assert_ok (fst (process_command ("Kind " ^ name ^ " type."))))
      names ;
    names
  in
  let check prefix n expected =
    start_web_session () ;
    let names = process_three prefix in
    State.Undo.back n ;
    List.iter2 (fun name present ->
        Alcotest.check Alcotest.bool
          (name ^ (if present then " is missing" else " should be gone"))
          true (has_kind name = present))
      names expected
  in
  check "u1" 1 [true ; true ; false] ;
  check "u2" 2 [true ; false ; false] ;
  check "u3" 3 [false ; false ; false]

let test_axiom_declaration () =
  let (status, msgs) = process_command "Axiom ax : true." in
  assert_ok status ;
  Alcotest.check (Alcotest.list Alcotest.string) "string lists differ" [] (error_messages msgs) ;
  Alcotest.check (Alcotest.list Alcotest.string) "string lists differ" ["ax"] !D.Setup.axioms ;
  Alcotest.check (Alcotest.list Alcotest.string) "string lists differ" [] !D.Setup.unfinished ;
  let (status, msgs) = process_command "Show ax." in
  assert_ok status ;
  assert_contains "Theorem ax" (system_messages msgs)

let test_thmod_virtual_import () =
  Source.add_virtual "Box.thmod" {|
Module Box[T].
  Kind box type.
  Type mk T -> box.
  Type p T -> prop.
End Box.
|} ;
  assert_ok (fst (process_command "Kind nat type.")) ;
  let (import_status, import_msgs) =
    process_command "Import Module B = \"Box\"[nat]."
  in
  if Result.is_error import_status then
    Alcotest.fail (String.concat "\n" (system_messages import_msgs)) ;
  Alcotest.check Alcotest.bool "box thmodc cache" true
    (Source.virtual_exists "Box.thmodc") ;
  Alcotest.check Alcotest.bool "box thmodc trusted" true
    (Source.is_thc_trusted "Box.thmodc") ;
  assert_ok (fst (process_command "Type c B.box.")) ;
  assert_ok (fst (process_command "Type d B.box."))

let test_interactive_thmod () =
  Source.add_virtual "List.thmod" {|
Module List.
  Kind lst type.
  Type lnil lst.
  Type lcons lst -> lst.
End List.
|} ;
  D.Setup.file_kind := `thmod ;
  D.Setup.input := "List.thmod" ;
  assert_ok (fst (process_command "Module List.")) ;
  assert_ok (fst (process_command "Kind lst type.")) ;
  assert_ok (fst (process_command "Type lnil lst.")) ;
  assert_ok (fst (process_command "Type lcons lst -> lst.")) ;
  assert_ok (fst (process_command "End List.")) ;
  Alcotest.check Alcotest.bool "thmod finished" true
    (Thmod.is_complete ())

let test_show_module () =
  Source.add_virtual "List.thmod" {|
Module List[T].
  Kind lst type.
  Type lnil lst.
  Axiom head : forall (xs:lst), xs = xs.
End List.
|} ;
  let (status, msgs) = process_command "Show Module \"List\"." in
  assert_ok status ;
  let text = String.concat "\n" (system_messages msgs) in
  assert_contains "Module List[T]." [text] ;
  assert_contains "Kind lst type." [text] ;
  assert_contains "End List." [text] ;
  assert_ok (fst (process_command "Module M.")) ;
  assert_ok (fst (process_command "Kind u type.")) ;
  assert_ok (fst (process_command "Type c u.")) ;
  assert_ok (fst (process_command "End M.")) ;
  let (status, msgs) = process_command "Show Module M." in
  assert_ok status ;
  assert_contains "Module M." (system_messages msgs) ;
  assert_contains "Type c u." (system_messages msgs) ;
  assert_ok (fst (process_command "Import Module I = M.")) ;
  let (status, msgs) = process_command "Show Module I." in
  assert_ok status ;
  assert_contains "Module I." (system_messages msgs) ;
  assert_contains "Type c u." (system_messages msgs) ;
  assert_ok (fst (process_command "Theorem t : true.")) ;
  assert_ok (fst (process_command "intros.")) ;
  let (status, msgs) = process_command "Show Module M." in
  assert_ok status ;
  assert_contains "Module M." (system_messages msgs) ;
  assert_ok (fst (process_command "search."))

let tests = suite "web_core" [
  test_case "virtual_source" (fun () -> with_session test_virtual_source) ;
  test_case "thc_cache_bound" (fun () -> with_session test_thc_cache_bound) ;
  test_case "output_collect" (fun () -> with_session test_output_collect) ;
  test_case "theorem_state" (fun () -> with_session test_theorem_state) ;
  test_case "undo_back_counts" (fun () -> with_session test_undo_back_counts) ;
  test_case "axiom_declaration" (fun () -> with_session test_axiom_declaration) ;
  test_case "thmod_virtual_import"
    (fun () -> with_session test_thmod_virtual_import) ;
  test_case "interactive_thmod"
    (fun () -> with_session test_interactive_thmod) ;
  test_case "show_module" (fun () -> with_session test_show_module) ;
]
