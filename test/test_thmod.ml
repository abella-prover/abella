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
   bytes written to [name.thmodc], or the collected error text. *)
let run_thmod dir name source =
  let path = Filename.concat dir (name ^ ".thmod") in
  write_file path source ;
  State.reload D.initial_snapshot ;
  Thmod.reset () ;
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
  D.Setup.thmod_name := None ;
  D.Setup.thmod_params := [] ;
  D.Setup.thmod_finished := false ;
  let module Src = (val Source.read_thmod path) in
  D.Setup.compiled := Some (module Src) ;
  D.Setup.lexbuf := Src.lex true ;
  Output.collect_mode () ;
  ignore (Output.drain ()) ;
  let rec drive () =
    try ignore (D.process1 ()) ; drive () with
    | D.AbellaExit 0 -> ()
    | D.AbellaExit n -> raise (D.AbellaExit n)
  in
  try
    drive () ;
    `Ok (read_file Src.thc_path)
  with
  | D.AbellaExit _ -> `Error (D.collected_messages ())
  | e -> `Error (Printexc.to_string e)

let native_compile_thmod dir name source =
  match run_thmod dir name source with
  | `Ok bytes -> bytes
  | `Error msg -> Alcotest.fail msg

let expect_thmod_error dir name source needle =
  match run_thmod dir name source with
  | `Ok _ -> Alcotest.fail ("expected an error containing " ^ needle)
  | `Error msg ->
      let found =
        let n = String.length needle in
        let rec spin i =
          i + n <= String.length msg &&
          (String.sub msg i n = needle || spin (i + 1))
        in
        spin 0
      in
      Alcotest.check Alcotest.bool
        ("expected error containing " ^ needle) true found

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
        ["u"; "c"; "p"; "refl"] exports ;
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
          | CDeclPred (["p"], [], ty) ->
              let has_T = ref false in
              Term.iter_ty begin function
                | Term.Tygenvar "T" -> has_T := true
                | _ -> ()
              end ty ;
              !has_T
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "declared predicate uses CDeclPred"
        true has_decl_pred
    end
  end

let test_nested_modules () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      let bytes = native_compile_thmod dir "Outer" {|
Module Outer[T].
  Kind u type.
  Type top u.
  Module Inner[U].
    Kind v type.
    Type inner U.
    Theorem id : forall (x:v), x = x.
    intros. search.
  End Inner.
  Module Empty.
  End Empty.
End Outer.
|} in
      let (name, params, content, nested, exports) =
        read_thmod_values bytes
      in
      Alcotest.check Alcotest.string "module name" "Outer" name ;
      Alcotest.check (Alcotest.list Alcotest.string) "parameters"
        ["T"] params ;
      Alcotest.check (Alcotest.list Alcotest.string) "nested modules"
        ["Inner"; "Empty"] nested ;
      Alcotest.check (Alcotest.list Alcotest.string) "exports"
        ["u"; "top"] exports ;
      let has_top_kind =
        List.exists (function CKind (["u"], _) -> true | _ -> false)
          content
      in
      let has_top_type =
        List.exists (function
            | CType (["top"], _, _) -> true
            | _ -> false) content
      in
      let has_nested =
        List.exists begin function
          | CKind ("Inner.v" :: _, _)
          | CType ("Inner.inner" :: _, _, _)
          | CTheorem ("Inner.id", _, _, _) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "top kind is exported" true has_top_kind ;
      Alcotest.check Alcotest.bool "top type is exported" true has_top_type ;
      Alcotest.check Alcotest.bool "nested items are not exported" false
        has_nested
    end
  end

let test_module_parameter_scoping () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      let bytes = native_compile_thmod dir "Param" {|
Module Param[T].
  Type p T -> prop.
  Type r T -> A -> prop.
  Define q : T -> prop by
    q X := p X.
  Define eq : A -> A -> prop by
    eq X X.
  Define mix : T -> A -> prop by
    mix X Y := p X.
End Param.
|} in
      let (_, params, content, _, _) = read_thmod_values bytes in
      Alcotest.check (Alcotest.list Alcotest.string) "parameters"
        ["T"] params ;
      let decl_pred =
        List.find_opt begin function
          | CDeclPred (["p"], _, _) -> true
          | _ -> false
        end content
      in
      begin match decl_pred with
      | Some (CDeclPred (_, typarams, _)) ->
          Alcotest.check (Alcotest.list Alcotest.string)
            "module parameter is not a local type parameter"
            [] typarams
      | _ -> Alcotest.fail "missing declared predicate p"
      end ;
      let has_define =
        List.exists begin function
          | CDefine (_, [], [("q", _)], _) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "definition has no local parameters"
        true has_define ;
      let has_polymorphic_define =
        List.exists begin function
          | CDefine (_, ["A"], [("eq", _)], _) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool
        "declaration-local parameter is preserved" true
        has_polymorphic_define ;
      let has_mixed_decl =
        List.exists begin function
          | CDeclPred (["r"], ["A"], _) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool
        "mixed declared predicate keeps only local parameters" true
        has_mixed_decl ;
      let has_mixed_define =
        List.exists begin function
          | CDefine (_, ["A"], [("mix", _)], _) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool
        "mixed definition keeps only local parameters" true
        has_mixed_define
    end
  end

let test_key_classification () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      let bytes = native_compile_thmod dir "Keys" {|
Module Keys.
  Kind u type.
  Type c u.
  Type p u -> prop.
  Type z prop.
  Define d : u -> prop by
    d X := p X.
  Theorem thm : forall (x:u), x = x.
  intros. search.
  Axiom ax : forall (x:u), p x -> p x.
End Keys.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let check_class label decl expected =
        Alcotest.check (Alcotest.option Alcotest.string) label
          (Some expected)
          (Option.map (function
               | Thmod.KindItem -> "kind"
               | Thmod.TypeItem -> "type"
               | Thmod.PredicateItem -> "predicate"
               | Thmod.DefineItem -> "define"
               | Thmod.TheoremItem -> "theorem"
               | Thmod.AxiomItem -> "axiom")
             (Thmod.class_of_compiled decl))
      in
      let find pred =
        try List.find pred content
        with Not_found -> Alcotest.fail "missing declaration"
      in
      check_class "ordinary type is not a key"
        (find (function CType (["c"], _, _) -> true | _ -> false))
        "type" ;
      check_class "declared predicate is a key"
        (find (function CDeclPred (["p"], _, _) -> true | _ -> false))
        "predicate" ;
      check_class "zero-argument predicate is a key"
        (find (function CDeclPred (["z"], _, _) -> true | _ -> false))
        "predicate" ;
      check_class "defined predicate is not a key"
        (find (function
             | CDefine (_, _, [("d", _)], _) -> true
             | _ -> false)) "define" ;
      check_class "theorem is not a key"
        (find (function
             | CTheorem ("thm", _, _, Finished) -> true
             | _ -> false)) "theorem" ;
      check_class "axiom is a key"
        (find (function
             | CTheorem ("ax", _, _, Axiomatic) -> true
             | _ -> false)) "axiom" ;
      let rigid =
        Thmod.rigid_predicates_of_decls content |> Term.Iset.elements
      in
      Alcotest.check (Alcotest.list Alcotest.string)
        "rigid predicate set" ["d"; "p"; "z"] rigid ;
      let keys =
        Thmod.keys_of_decls content
        |> List.map (fun it -> it.Thmod.item_name)
      in
      Alcotest.check (Alcotest.list Alcotest.string)
        "remaining keys" ["p"; "z"; "ax"] keys
    end
  end

let test_name_scoping_errors () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      expect_thmod_error dir "Shadow" {|
Module Shadow.
  Kind u type.
  Module Bar.
    Kind u type.
  End Bar.
End Shadow.
|} "shadows a declaration in an enclosing module" ;
      expect_thmod_error dir "Sibling" {|
Module Sibling.
  Module Bar.
    Kind v type.
  End Bar.
  Module Baz.
    Kind w type.
    Type d Bar.v.
  End Baz.
End Sibling.
|} "Unknown module Bar" ;
      expect_thmod_error dir "Parent" {|
Module Parent.
  Kind u type.
  Module Bar.
    Type d Parent.u.
  End Bar.
End Parent.
|} "Unknown module Parent" ;
      expect_thmod_error dir "ParamShadow" {|
Module ParamShadow[T].
  Module Bar[T].
    Type q prop.
  End Bar.
End ParamShadow.
|} "shadows an enclosing parameter" ;
      expect_thmod_error dir "ParamList" {|
Module ParamList[T].
  Theorem t [T] : forall (x:prop), x -> x.
  intros. search.
End ParamList.
|} "may not be listed" ;
      expect_thmod_error dir "DupNested" {|
Module DupNested.
  Module Bar.
  End Bar.
  Module Bar.
  End Bar.
End DupNested.
|} "already declared in this module" ;
      expect_thmod_error dir "BadNestedEnd" {|
Module BadNestedEnd.
  Module Bar.
  End Baz.
End BadNestedEnd.
|} "does not match Module Bar" ;
      expect_thmod_error dir "ModuleFinal" {|
Module ModuleFinal.
  Module Bar.
  End Bar.
  Type c ModuleFinal.Bar.
End ModuleFinal.
|} "Module name Bar is not an item" ;
      expect_thmod_error dir "ParamFinal" {|
Module ParamFinal[T].
  Type c ParamFinal.T.
End ParamFinal.
|} "Module parameter T is not an item"
    end
  end

let test_split_names () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      let bytes = native_compile_thmod dir "Spl" {|
Module Spl.
  Kind u type.
  Type p u -> prop.
  Axiom ax : forall (x:u), p x /\ p x.
  Split ax.
  Module Inner.
    Axiom inn : forall (x:u), p x /\ p x.
    Split inn.
  End Inner.
End Spl.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let has_generated name =
        List.exists begin function
          | CTheorem (n, _, _, Axiomatic) -> n = name
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "first split name is local" true
        (has_generated "ax1") ;
      Alcotest.check Alcotest.bool "second split name is local" true
        (has_generated "ax2") ;
      Alcotest.check Alcotest.bool "nested split stays nested" false
        (has_generated "Inner.inn1")
    end
  end

let test_phase4_checks () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      expect_thmod_error dir "HoKey" {|
Module HoKey.
  Type p (prop -> prop) -> prop.
End HoKey.
|} "may not take an argument containing prop" ;
      expect_thmod_error dir "Strat" {|
Module Strat.
  Define d : prop by
    d := d -> d.
End Strat.
|} "might not be stratified" ;
      expect_thmod_error dir "Frozen" {|
Module Frozen[T].
  Kind u type.
  Type c u.
  Type p T -> prop.
  Theorem bad : p c.
  intros. search.
End Frozen.
|} "Expression has type u but is used here with type T" ;
      let bytes = native_compile_thmod dir "HoDefine" {|
Module HoDefine.
  Define h : (prop -> prop) -> prop by
    h (x \ x).
End HoDefine.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let has_ho_define =
        List.exists begin function
          | CDefine (_, [], [("h", _)], _) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "higher-order Define is allowed" true
        has_ho_define ;
      let bytes = native_compile_thmod dir "Poly" {|
Module Poly.
  Type p A -> prop.
  Define d : prop by
    d := p d.
End Poly.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let has_poly_pred =
        List.exists begin function
          | CDeclPred (["p"], ["A"], _) -> true
          | _ -> false
        end content
      in
      let has_poly_use =
        List.exists begin function
          | CDefine (_, [], [("d", _)], _) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool
        "polymorphic declared predicate keeps its local parameter" true
        has_poly_pred ;
      Alcotest.check Alcotest.bool
        "polymorphic declared predicate can be used at prop" true
        has_poly_use ;
      let bytes = native_compile_thmod dir "Rigid" {|
Module Rigid.
  Kind u type.
  Type c u.
  Type p u -> prop.
  Theorem t : p c -> p c.
  intros. search.
End Rigid.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let has_rigid_theorem =
        List.exists begin function
          | CTheorem ("t", [], _, Finished) -> true
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool
        "internal Kind types remain rigid constants" true
        has_rigid_theorem
    end
  end

let tests =
  suite "thmod" [
      test_case "read_thmod defaults" test_read_thmod_defaults ;
      test_case "artifact layout" test_thmod_artifact_layout ;
      test_case "parameters are recorded" test_thmod_parameters_are_recorded ;
      test_case "nested modules" test_nested_modules ;
      test_case "module parameter scoping" test_module_parameter_scoping ;
      test_case "key classification" test_key_classification ;
      test_case "name scoping errors" test_name_scoping_errors ;
      test_case "split names" test_split_names ;
      test_case "phase 4 checks" test_phase4_checks ;
    ]
