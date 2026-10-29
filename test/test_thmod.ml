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
  let cleanup () =
    Source.clear_virtual () ;
    Source.clear_thc_trust () ;
    Accumulate.clear_specification_cache ()
  in
  Fun.protect ~finally:cleanup (fun () -> D.Setup.with_saved f)

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
    | D.AbellaExit 0 -> ()
    | D.AbellaExit n -> raise (D.AbellaExit n)
  in
  try
    drive D.Process_top ;
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
    let module Src = (val Thmod.read "mods/Foo.thmod") in
    Alcotest.check Alcotest.string "path" "mods/Foo.thmod" Src.path ;
    Alcotest.check Alcotest.string "artifact path"
      "mods/Foo.thmodc" Src.thc_path ;
    Alcotest.check Alcotest.bool "is stale" true Src.is_stale ;
    Source.add_virtual "mods/Foo.thmodc" "artifact" ;
    Source.set_thc_trusted "mods/Foo.thmodc" true ;
    let module Src = (val Thmod.read "mods/Foo.thmod") in
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

let test_import_basic () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      ignore (native_compile_thmod dir "Box" {|
Module Box[T].
  Kind box type.
  Type mk T -> box.
  Type p T -> prop.
  Axiom ax : forall (x:T), p x.
End Box.
|}) ;
      let bytes = native_compile_thmod dir "Use" {|
Module Use.
  Kind u type.
  Type c u.
  Import Module B = "Box"[u].
  Theorem t : B.p c -> B.p c.
  intros. search.
End Use.
|} in
      let (_, _, content, _, exports) = read_thmod_values bytes in
      let has pred =
        List.exists pred content
      in
      Alcotest.check Alcotest.bool "imported kind" true
        (has (function CKind (["B.box"], _) -> true | _ -> false)) ;
      Alcotest.check Alcotest.bool "imported constant" true
        (has (function CType (["B.mk"], _, _) -> true | _ -> false)) ;
      Alcotest.check Alcotest.bool "imported predicate" true
        (has (function CDeclPred (["B.p"], [], _) -> true | _ -> false)) ;
      Alcotest.check Alcotest.bool "imported axiom" true
        (has (function
             | CTheorem ("B.ax", _, _, Axiomatic) -> true
             | _ -> false)) ;
      Alcotest.check (Alcotest.list Alcotest.string) "exports"
        ["u"; "c"; "B.box"; "B.mk"; "B.p"; "B.ax"; "t"]
        exports
    end
  end

let test_import_with () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      ignore (native_compile_thmod dir "Eq" {|
Module Eq[T].
  Type eq T -> T -> prop.
  Axiom refl : forall (x:T), eq x x.
End Eq.
|}) ;
      let bytes = native_compile_thmod dir "EqUse" {|
Module EqUse.
  Kind u type.
  Type c u.
  Define eq_u : u -> u -> prop by
    eq_u X X.
  Theorem refl_u : forall (x:u), eq_u x x.
  intros. search.
  Import Module E = "Eq"[u] with eq := eq_u, refl := refl_u.
  Theorem t : forall (x:u), eq_u x x.
  intros. apply E.refl. search.
End EqUse.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let has pred = List.exists pred content in
      Alcotest.check Alcotest.bool "mapped predicate is removed" false
        (has (function CDeclPred (["E.eq"], _, _) -> true | _ -> false)) ;
      Alcotest.check Alcotest.bool "mapped axiom aliases the theorem" true
        (has (function
             | CTheorem ("E.refl", [], _, Finished) -> true
             | _ -> false))
    end
  end

let test_import_transitive_nested () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      ignore (native_compile_thmod dir "Box2" {|
Module Box2[T].
  Kind box type.
  Type p T -> prop.
End Box2.
|}) ;
      ignore (native_compile_thmod dir "Trans" {|
Module Trans.
  Kind u type.
  Import Module Box = "Box2"[u].
End Trans.
|}) ;
      let bytes = native_compile_thmod dir "UseTrans" {|
Module UseTrans.
  Import Module T = "Trans".
  Type h T.Box.box -> prop.
End UseTrans.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let has pred = List.exists pred content in
      Alcotest.check Alcotest.bool "transitive kind" true
        (has (function CKind (["T.Box.box"], _) -> true | _ -> false)) ;
      Alcotest.check Alcotest.bool "transitive predicate" true
        (has (function
             | CDeclPred (["T.Box.p"], [], _) -> true
             | _ -> false)) ;
      ignore (native_compile_thmod dir "Outer2" {|
Module Outer2.
  Kind u type.
  Type c u.
  Module Inner[U].
    Kind inner type.
    Type d inner.
    Type p U -> prop.
  End Inner.
  Import Module I = Inner[u].
End Outer2.
|}) ;
      let bytes = native_compile_thmod dir "UseOuter2" {|
Module UseOuter2.
  Import Module O = "Outer2".
  Type h O.I.inner -> prop.
  Theorem t : O.I.p O.c -> O.I.p O.c.
  intros. search.
End UseOuter2.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let has pred = List.exists pred content in
      Alcotest.check Alcotest.bool "nested kind" true
        (has (function CKind (["O.I.inner"], _) -> true | _ -> false)) ;
      Alcotest.check Alcotest.bool "nested predicate" true
        (has (function
             | CDeclPred (["O.I.p"], [], _) -> true
             | _ -> false))
    end
  end

let test_import_dotted_key () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      ignore (native_compile_thmod dir "Outer3" {|
Module Outer3[T].
  Module Inner.
    Type q T -> prop.
  End Inner.
  Import Module I = Inner.
End Outer3.
|}) ;
      begin match run_thmod dir "UseOuter3" {|
Module UseOuter3.
  Kind u type.
  Type r u -> prop.
  Import Module O = "Outer3"[u] with I.q := r.
End UseOuter3.
|} with
      | `Ok _ -> ()
      | `Error msg -> Alcotest.fail msg
      end
    end
  end

let test_import_nested_strict () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      ignore (native_compile_thmod dir "NestA" {|
Module NestA.
  Kind u type.
  Module N.
    Type p u -> prop.
  End N.
  Import Module N.
End NestA.
|}) ;
      ignore (native_compile_thmod dir "NestB" {|
Module NestB.
  Kind u type.
  Module N.
    Type p u -> prop.
  End N.
End NestB.
|}) ;
      begin match run_thmod dir "UseNestA" {|
Module UseNestA.
  Import Module "NestA".
  Type c NestA.u.
  Theorem t : NestA.N.p c -> NestA.N.p c.
  intros. search.
End UseNestA.
|} with
      | `Ok _ -> ()
      | `Error msg -> Alcotest.fail msg
      end ;
      expect_thmod_error dir "UseNestB" {|
Module UseNestB.
  Import Module "NestB".
  Type c NestB.u.
  Theorem t : NestB.N.p c -> NestB.N.p c.
  intros. search.
End UseNestB.
|} "Unknown item NestB.N.p"
    end
  end

let test_import_multiple_instances () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      ignore (native_compile_thmod dir "Box3" {|
Module Box3[T].
  Kind box type.
  Type mk T -> box.
End Box3.
|}) ;
      let bytes = native_compile_thmod dir "Multi" {|
Module Multi.
  Kind u type.
  Kind v type.
  Import Module B1 = "Box3"[u].
  Import Module B2 = "Box3"[v].
  Type f B1.box -> prop.
  Type g B2.box -> prop.
End Multi.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let has pred = List.exists pred content in
      Alcotest.check Alcotest.bool "first internal type" true
        (has (function CKind (["B1.box"], _) -> true | _ -> false)) ;
      Alcotest.check Alcotest.bool "second internal type" true
        (has (function CKind (["B2.box"], _) -> true | _ -> false))
    end
  end

let test_import_errors () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      ignore (native_compile_thmod dir "Box5" {|
Module Box5[T].
  Kind box type.
  Type p T -> prop.
End Box5.
|}) ;
      ignore (native_compile_thmod dir "M5" {|
Module M5[T].
  Type p T -> prop.
  Type q T -> prop.
  Axiom ax : forall (x:T), p x -> p x.
End M5.
|}) ;
      ignore (native_compile_thmod dir "Box6" {|
Module Box6[T].
  Kind box type.
  Type p box -> prop.
End Box6.
|}) ;
      ignore (native_compile_thmod dir "Unfin5" {|
Module Unfin5[T].
  Type p T -> prop.
  Axiom ax : forall (x:T), p x.
End Unfin5.
|}) ;
      ignore (native_compile_thmod dir "Eq5" {|
Module Eq5[T].
  Type eq T -> T -> prop.
  Axiom refl : forall (x:T), eq x x.
End Eq5.
|}) ;
      expect_thmod_error dir "Arity" {|
Module Arity.
  Import Module "Box5".
End Arity.
|} "expects 1 type arguments" ;
      expect_thmod_error dir "Alias" {|
Module Alias.
  Kind u type.
  Import Module B = "Box5"[u].
  Import Module B = "Box5"[u].
End Alias.
|} "already imported" ;
      expect_thmod_error dir "PropArg" {|
Module PropArg.
  Import Module "Box5"[prop].
End PropArg.
|} "may not contain prop" ;
      expect_thmod_error dir "FreeArg" {|
Module FreeArg.
  Import Module "Box5"[A].
End FreeArg.
|} "free type variable" ;
      expect_thmod_error dir "UnknownKey" {|
Module UnknownKey.
  Kind u type.
  Import Module B = "Box5"[u] with nope := u.
End UnknownKey.
|} "Unknown with key" ;
      expect_thmod_error dir "DupKey" {|
Module DupKey.
  Kind u type.
  Import Module B = "Box5"[u] with p := u, p := u.
End DupKey.
|} "Duplicate with key" ;
      expect_thmod_error dir "InstanceBrackets" {|
Module InstanceBrackets.
  Kind u type.
  Import Module B = "Box5"[u].
  Import Module C = B[u].
End InstanceBrackets.
|} "already instantiated" ;
      expect_thmod_error dir "NonKey" {|
Module NonKey.
  Kind u type.
  Import Module B = "Box5"[u] with box := u.
End NonKey.
|} "not a declared predicate or axiom" ;
      expect_thmod_error dir "WrongValue" {|
Module WrongValue.
  Kind u type.
  Import Module B = "Box5"[u] with p := u.
End WrongValue.
|} "not a predicate or axiom" ;
      expect_thmod_error dir "Collision" {|
Module Collision.
  Kind u type.
  Type p u -> prop.
  Module Inner.
    Type q u -> prop.
    Axiom ax : forall (x:u), q x -> p x.
  End Inner.
  Import Module I = Inner with q := p.
End Collision.
|} "already occurs in the declarations" ;
      expect_thmod_error dir "Staged" {|
Module Staged.
  Kind u type.
  Type r u -> prop.
  Import Module M1 = "M5"[u] with p := r.
  Import Module M2 = M1 with q := r.
End Staged.
|} "already occurs in the declarations" ;
      expect_thmod_error dir "Unfinished" {|
Module Unfinished.
  Kind u type.
  Type r u -> prop.
  Theorem skip_t : forall (x:u), r x.
  intros. skip.
  Import Module U = "Unfin5"[u] with p := r, ax := skip_t.
End Unfinished.
|} "unfinished" ;
      expect_thmod_error dir "SchemeMismatch" {|
Module SchemeMismatch.
  Kind u type.
  Type eq_u u -> u -> prop.
  Import Module B = "Box5"[u] with p := eq_u.
End SchemeMismatch.
|} "same type" ;
      expect_thmod_error dir "PairDistinct" {|
Module PairDistinct.
  Kind u type.
  Type r u -> prop.
  Import Module M = "M5"[u] with p := r, q := r.
End PairDistinct.
|} "pairwise distinct" ;
      expect_thmod_error dir "AxiomMismatch" {|
Module AxiomMismatch.
  Kind u type.
  Define eq_u : u -> u -> prop by
    eq_u X X.
  Theorem wrong : forall (x:u), eq_u x x -> eq_u x x.
  intros. search.
  Import Module E = "Eq5"[u] with eq := eq_u, refl := wrong.
End AxiomMismatch.
|} "same statement" ;
      expect_thmod_error dir "DuplicateImport" {|
Module DuplicateImport.
  Kind u type.
  Import Module "Box5"[u].
  Import Module "Box5"[u].
End DuplicateImport.
|} "already been imported" ;
      expect_thmod_error dir "EarlierInstance" {|
Module EarlierInstance.
  Kind u type.
  Kind v type.
  Import Module B = "Box5"[u].
  Import Module C = "Box5"[v] with p := B.p.
End EarlierInstance.
|} "already occurs in the declarations" ;
      expect_thmod_error dir "InternalKey" {|
Module InternalKey.
  Kind u type.
  Type q u -> prop.
  Import Module B = "Box6"[u] with p := q.
End InternalKey.
|} "target-local type" ;
    end
  end

let test_tags_split_and_import () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      let bytes = native_compile_thmod dir "Tags" {|
Module Tags.
  Kind u type.
  Type p u -> prop.
  Axiom ax : forall (x:u), p x /\ p x.
  Split ax.
  Theorem skip_t : forall (x:u), p x /\ p x.
  intros. skip.
  Split skip_t.
End Tags.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let has_tag name tag =
        List.exists begin function
          | CTheorem (n, _, _, fin) -> n = name && fin = tag
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "axiom tag" true
        (has_tag "ax" Axiomatic) ;
      Alcotest.check Alcotest.bool "split axiom tag" true
        (has_tag "ax1" Axiomatic) ;
      Alcotest.check Alcotest.bool "skip tag" true
        (has_tag "skip_t" Unfinished) ;
      Alcotest.check Alcotest.bool "split skip tag" true
        (has_tag "skip_t1" Unfinished) ;
      let axioms = List.unique !(D.Setup.axioms) in
      let unfinished = List.unique !(D.Setup.unfinished) in
      Alcotest.check (Alcotest.list Alcotest.string) "reported axioms"
        ["ax"] (List.sort String.compare axioms) ;
      Alcotest.check (Alcotest.list Alcotest.string) "reported skips"
        ["skip_t"; "skip_t1"; "skip_t2"]
        (List.sort String.compare unfinished) ;
      let bytes = native_compile_thmod dir "UseTags" {|
Module UseTags.
  Import Module T = "Tags".
End UseTags.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let has_tag name tag =
        List.exists begin function
          | CTheorem (n, _, _, fin) -> n = name && fin = tag
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "imported axiom tag" true
        (has_tag "T.ax" Axiomatic) ;
      Alcotest.check Alcotest.bool "imported split axiom tag" true
        (has_tag "T.ax1" Axiomatic) ;
      Alcotest.check Alcotest.bool "imported skip tag" true
        (has_tag "T.skip_t" Unfinished) ;
      let axioms = List.unique !(D.Setup.axioms) in
      let unfinished = List.unique !(D.Setup.unfinished) in
      Alcotest.check Alcotest.bool "imported axioms reported" true
        (List.mem "T.ax1" axioms) ;
      Alcotest.check Alcotest.bool "imported skips not reported" false
        (List.mem "T.skip_t" unfinished)
    end
  end

let test_tags_alias () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      ignore (native_compile_thmod dir "Eq6" {|
Module Eq6[T].
  Type eq T -> T -> prop.
  Axiom refl : forall (x:T), eq x x.
End Eq6.
|}) ;
      let bytes = native_compile_thmod dir "UseEq6" {|
Module UseEq6.
  Kind u type.
  Define eq_u : u -> u -> prop by
    eq_u X X.
  Theorem refl_u : forall (x:u), eq_u x x.
  intros. search.
  Define eq_v : u -> u -> prop by
    eq_v X X.
  Axiom refl_ax : forall (x:u), eq_v x x.
  Import Module A = "Eq6"[u] with eq := eq_u, refl := refl_u.
  Import Module B = "Eq6"[u] with eq := eq_v, refl := refl_ax.
End UseEq6.
|} in
      let (_, _, content, _, _) = read_thmod_values bytes in
      let has_tag name tag =
        List.exists begin function
          | CTheorem (n, _, _, fin) -> n = name && fin = tag
          | _ -> false
        end content
      in
      Alcotest.check Alcotest.bool "finished alias tag" true
        (has_tag "A.refl" Finished) ;
      Alcotest.check Alcotest.bool "axiomatic alias tag" true
        (has_tag "B.refl" Axiomatic) ;
      let axioms = List.unique !(D.Setup.axioms) in
      Alcotest.check Alcotest.bool "finished alias not reported" false
        (List.mem "A.refl" axioms) ;
      Alcotest.check Alcotest.bool "axiomatic alias reported" true
        (List.mem "B.refl" axioms)
    end
  end

let test_no_sequents () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      expect_thmod_error dir "SeqTheorem" {|
Module SeqTheorem.
  Theorem bad : forall (x:o), { x |- x }.
  intros. search.
End SeqTheorem.
|} "Specification logic sequents are not allowed" ;
      expect_thmod_error dir "SeqDefine" {|
Module SeqDefine.
  Define q : o -> prop by
    q X := { X |- X }.
End SeqDefine.
|} "Specification logic sequents are not allowed" ;
      ignore (native_compile_thmod dir "ObjTy" {|
Module ObjTy.
  Type f o -> o.
  Type p o -> prop.
End ObjTy.
|})
    end
  end

let test_show_module_summary () =
  with_session begin fun () ->
    with_temp_dir begin fun dir ->
      let bytes = native_compile_thmod dir "List" {|
Module List[T].
  Kind lst type.
  Type lnil lst.
  Type lcons T -> lst -> lst.
  Type contains T -> lst -> prop.
  Axiom head : forall (x:T) (xs:lst), contains x (lcons x xs).
End List.
|} in
      let (name, params, content, _, _) = read_thmod_values bytes in
      let summary =
        Thmod_import.summary_to_string ~name ~params ~prefix:[] content in
      let expected = String.concat "\n" [
        "Module List[T]." ;
        "  Kind lst type." ;
        "  Type lnil lst." ;
        "  Type lcons T -> lst -> lst." ;
        "  Type contains T -> lst -> prop." ;
        "  Axiom head : forall x xs, contains x (lcons x xs)." ;
        "End List." ;
        "" ;
      ] in
      Alcotest.check Alcotest.string "summary" expected summary
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
      test_case "no sequents" test_no_sequents ;
      test_case "show module summary" test_show_module_summary ;
      test_case "import basic" test_import_basic ;
      test_case "import with" test_import_with ;
      test_case "import transitive nested" test_import_transitive_nested ;
      test_case "import nested strict" test_import_nested_strict ;
      test_case "import dotted key" test_import_dotted_key ;
      test_case "import multiple instances" test_import_multiple_instances ;
      test_case "import errors" test_import_errors ;
      test_case "tags split and import" test_tags_split_and_import ;
      test_case "tags alias" test_tags_alias ;
    ]
