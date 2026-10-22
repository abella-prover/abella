(* Tests for the browser-facing core: virtual sources, collected output,
   the generated .thc cache, and source imports. *)

open OUnit
open Abella_lib
open Abella_types
open Extensions
open Test_helper

module D = Abella_driver

let web_module = {|
Kind tm type.
Type app tm -> tm -> tm.

Define is_app : tm -> prop by
  is_app (app A B).

Theorem mod_ok : forall A B, is_app (app A B).
intros. search.
|}

let start_web_session () =
  State.reload D.initial_snapshot ;
  State.Undo.set_enabled true ;
  State.Undo.reset () ;
  Accumulate.clear_specification_cache () ;
  Typing.clause_map := Term.Itab.empty ;
  Source.clear_virtual () ;
  Source.clear_thc_trust () ;
  D.compiling := [] ;
  D.Setup.mode := `interactive ;
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
  let snap = State.snapshot () in
  let dest = !Output.dest in
  let clause_map = !Typing.clause_map in
  let compiling = !D.compiling in
  let on_import = !D.on_import in
  let mode = !D.Setup.mode in
  let annotate = !D.Setup.annotate in
  let recurse = !D.Setup.recurse in
  let input = !D.Setup.input in
  let lexbuf = !D.Setup.lexbuf in
  let compiled = !D.Setup.compiled in
  let unfinished = !D.Setup.unfinished in
  let import_mode = !D.Setup.import_mode in
  let trust_compiled = !D.Setup.trust_compiled in
  let restore () =
    State.reload snap ;
    Output.dest := dest ;
    Typing.clause_map := clause_map ;
    D.compiling := compiling ;
    D.on_import := on_import ;
    D.Setup.mode := mode ;
    D.Setup.annotate := annotate ;
    D.Setup.recurse := recurse ;
    D.Setup.input := input ;
    D.Setup.lexbuf := lexbuf ;
    D.Setup.compiled := compiled ;
    D.Setup.unfinished := unfinished ;
    D.Setup.import_mode := import_mode ;
    D.Setup.trust_compiled := trust_compiled ;
    Source.clear_virtual () ;
    Source.clear_thc_trust () ;
    Accumulate.clear_specification_cache ()
  in
  Fun.protect ~finally:restore (fun () ->
    start_web_session () ;
    f ())

let process_command command =
  let lb = Lexing.from_string command in
  lb.Lexing.lex_curr_p <- {
    lb.Lexing.lex_curr_p with
    Lexing.pos_fname = !D.Setup.input
  } ;
  D.Setup.lexbuf := lb ;
  let status =
    try D.process1 () with
    | D.AbellaExit 0 -> `ok
    | D.AbellaExit _ -> `error
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

let assert_ok = function
  | `ok -> ()
  | `error -> assert_failure "command failed"

let assert_contains needle haystack =
  let found = List.exists begin fun text ->
      let n = String.length needle and h = String.length text in
      let rec spin i =
        i + n <= h && (String.sub text i n = needle || spin (i + 1))
      in
      spin 0
    end haystack
  in
  assert_bool ("expected message containing " ^ needle) found

let read_thc_values bytes =
  let buf = Bytes.unsafe_of_string bytes in
  let pos = ref 0 in
  let read () =
    let v = Marshal.from_string bytes !pos in
    pos := !pos + Marshal.total_size buf !pos ;
    v
  in
  ignore (read () : Digest.t) ;
  ignore (read () : string) ;
  ( (read () : Typing.sign),
    (read () : clause list),
    (read () : string list),
    (read () : compiled list) )

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

(* Compile [web_module] the way the native CLI does, and return the bytes
   of the resulting .thc file. *)
let native_compile_module () =
  let dir = Filename.temp_file "abella-web-test" "" in
  Sys.remove dir ;
  Unix.mkdir dir 0o700 ;
  Fun.protect ~finally:(fun () -> remove_tree dir) begin fun () ->
    let path = Filename.concat dir "mod.thm" in
    let thc = Filename.concat dir "mod.thc" in
    write_file path web_module ;
    State.reload D.initial_snapshot ;
    State.Undo.set_enabled false ;
    D.compiling := [] ;
    D.Setup.mode := `batch ;
    D.Setup.annotate := false ;
    D.Setup.recurse := false ;
    D.Setup.import_mode := `thc ;
    D.Setup.trust_compiled := false ;
    D.Setup.unfinished := [] ;
    D.Setup.input := Filename.concat dir "<dummy>.thm" ;
    let module Thm = (val Source.read_thm ~thc path) in
    D.Setup.compiled := Some (module Thm) ;
    D.Setup.lexbuf := Thm.lex true ;
    Output.collect_mode () ;
    ignore (Output.drain ()) ;
    let rec drive () =
      try ignore (D.process1 ()) ; drive () with
      | D.AbellaExit 0 -> ()
      | D.AbellaExit n -> assert_failure ("native compile exited " ^ string_of_int n)
    in
    drive () ;
    read_file thc
  end

let test_virtual_source () =
  assert_bool "canon strip ./" (Source.canon "./a/b.thm" = "a/b.thm") ;
  assert_bool "canon collapse dot" (Source.canon "a/./b.thm" = "a/b.thm") ;
  assert_bool "canon collapse dotdot" (Source.canon "a/x/../b.thm" = "a/b.thm") ;
  Source.add_virtual "./a/b.thm" "contents" ;
  assert_bool "virtual exists" (Source.virtual_exists "a/b.thm") ;
  assert_string_equal "contents" (Source.virtual_contents "a/b.thm") ;
  let module Src = (val Source.read "a/b.thm") in
  assert_string_equal "a/b.thm" Src.path ;
  assert_equal ~printer:(function Some d -> d | None -> "None") (Some "a") Src.dir ;
  assert_equal ~printer:string_of_float 0. Src.mtime ;
  let lb = Src.lex true in
  assert_string_equal "a/b.thm" lb.Lexing.lex_curr_p.Lexing.pos_fname ;
  assert_bool "missing file" begin
    try ignore (Source.read "nope.thm") ; false with Failure _ -> true
  end ;
  let bytes = "\000\001\255\254thc" in
  Source.add_virtual "gen/binary.thc" bytes ;
  assert_string_equal bytes (Source.virtual_contents "gen/binary.thc") ;
  Source.clear_virtual () ;
  assert_bool "cleared" (not (Source.virtual_exists "a/b.thm"))

let test_output_collect () =
  Output.collect_mode () ;
  ignore (Output.drain ()) ;
  Output.msg_printf "one" ;
  Output.msg_printf ~severity:Error "two" ;
  let msgs = Output.drain () in
  assert_int_equal 2 (List.length msgs) ;
  let texts = system_messages msgs in
  assert_string_list_equal ["one" ; "two"] texts ;
  let severities = List.filter_map begin function
      | `Assoc fields -> begin
          match List.assoc_opt "severity" fields with
          | Some (`String s) -> Some s
          | _ -> None
        end
      | _ -> None
    end msgs in
  assert_string_list_equal ["info" ; "error"] severities ;
  assert_int_equal 0 (List.length (Output.drain ()))

let test_source_import_cache () =
  Source.add_virtual "main.thm" "" ;
  Source.add_virtual "mod.thm" web_module ;
  let hits = ref [] in
  D.on_import := Some (fun name -> hits := name :: !hits) ;
  let (status, msgs) = process_command "Import \"mod\"." in
  assert_ok status ;
  assert_bool "generated thc exists" (Source.virtual_exists "mod.thc") ;
  assert_bool "generated thc trusted" (Source.is_thc_trusted "mod.thc") ;
  assert_string_list_equal ["mod"] !hits ;
  assert_string_list_equal [] (error_messages msgs) ;

  (* Rewind over the import; the generated .thc stays in the virtual FS. *)
  assert_ok (try State.Undo.back 1 ; `ok with Failure _ -> `error) ;
  hits := [] ;
  let (status, _) = process_command "Import \"mod\"." in
  assert_ok status ;
  assert_string_list_equal [] !hits ;

  let (status, msgs) = process_command "Import \"nope\"." in
  assert_bool "missing import fails" (status = `error) ;
  assert_contains "Opening: ./nope.thm" (system_messages msgs)

let test_values_match_native () =
  let native = native_compile_module () in
  start_web_session () ;
  Source.add_virtual "main.thm" "" ;
  Source.add_virtual "mod.thm" web_module ;
  let (status, _) = process_command "Import \"mod\"." in
  assert_ok status ;
  let generated = Source.virtual_contents "mod.thc" in
  let (ns, nc, np, nt) = read_thc_values native in
  let (ws, wc, wp, wt) = read_thc_values generated in
  assert_bool "spec sign differs" (ns = ws) ;
  assert_bool "spec clauses differ" (nc = wc) ;
  assert_bool "predicates differ" (np = wp) ;
  assert_bool "compiled content differs" (nt = wt)

let test_virtual_native_thc () =
  let native = native_compile_module () in
  start_web_session () ;
  Source.add_virtual "main.thm" "" ;
  Source.add_virtual "mod.thm" web_module ;
  Source.add_virtual "mod.thc" native ;
  Source.set_thc_trusted "mod.thc" true ;
  let hits = ref [] in
  D.on_import := Some (fun name -> hits := name :: !hits) ;
  let (status, _) = process_command "Import \"mod\"." in
  assert_ok status ;
  assert_string_list_equal [] !hits ;
  let (status, _) = process_command
      "Theorem root_ok : forall A B, is_app (app A B)." in
  assert_ok status ;
  assert_ok (fst (process_command "intros.")) ;
  let (status, msgs) = process_command "search." in
  assert_ok status ;
  assert_contains "Proof completed" (system_messages msgs)

let test_nested_imports () =
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
  D.on_import := Some (fun name -> hits := name :: !hits) ;
  assert_ok (fst (process_command "Import \"outer\".")) ;
  assert_bool "inner thc" (Source.is_thc_trusted "inner.thc") ;
  assert_bool "outer thc" (Source.is_thc_trusted "outer.thc") ;
  (* The outer progress hook fires before its sandbox compiles inner. *)
  assert_string_list_equal ["inner" ; "outer"] !hits

let test_import_cycle () =
  Source.add_virtual "main.thm" "" ;
  Source.add_virtual "a.thm" "Import \"b\"." ;
  Source.add_virtual "b.thm" "Import \"a\"." ;
  let (status, msgs) = process_command "Import \"a\"." in
  assert_bool "cycle fails" (status = `error) ;
  assert_contains "Cyclic import" (system_messages msgs)

let tests = "web_core" >::: [
  "virtual_source" >:: (fun () -> with_session test_virtual_source) ;
  "output_collect" >:: (fun () -> with_session test_output_collect) ;
  "source_import_cache" >:: (fun () -> with_session test_source_import_cache) ;
  "values_match_native" >:: (fun () -> with_session test_values_match_native) ;
  "virtual_native_thc" >:: (fun () -> with_session test_virtual_native_thc) ;
  "nested_imports" >:: (fun () -> with_session test_nested_imports) ;
  "import_cycle" >:: (fun () -> with_session test_import_cycle) ;
]
