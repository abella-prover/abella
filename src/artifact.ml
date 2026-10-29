(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                            en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Artifact codecs, loading policy, and shared compiled-declaration
   installation for .thc and .thmodc files. *)

open Term
open Typing
open Abella_types
open Extensions

type 'a spec = {
  file_kind : [`thm | `thmod] ;
  suffix : string ;
  compiled_suffix : string ;
  compiling_key : modname:string -> string ;
  extract : unit -> 'a ;
  encode : 'a -> Obj.t list ;
  decode : (unit -> Obj.t) -> 'a ;
}

let digest_placeholder () = Digest.string Version.version

let marshal_bytes (values : Obj.t list) =
  let buf = Buffer.create 4096 in
  List.iter (fun v -> Buffer.add_string buf (Marshal.to_string v [])) values ;
  Buffer.contents buf

let marshal_reader (s : string) : unit -> 'a =
  let buf = Bytes.unsafe_of_string s in
  let pos = ref 0 in
  fun () ->
    let v = Marshal.from_string s !pos in
    pos := !pos + Marshal.total_size buf !pos ;
    v

let to_bytes ?digest spec art =
  let digest = Option.value digest ~default:(digest_placeholder ()) in
  marshal_bytes
    (Obj.repr digest :: Obj.repr Version.version :: spec.encode art)

let write_compiled spec (module Compiled : Source.COMPILED) =
  let art = spec.extract () in
  Compiled.marshal (Lazy.force Version.self_digest) ;
  Compiled.marshal Version.version ;
  List.iter Compiled.marshal (spec.encode art) ;
  Compiled.close ()

let read_header_and_body spec bytes =
  let read = marshal_reader bytes in
  let digest = (read () : Digest.t) in
  let version = (read () : string) in
  let art = spec.decode read in
  (digest, version, art)

let recompile ~path ~out_path ~thc_path =
  if not !Driver_setup.recurse then
    failwithf "Recursive invocation of Abella prevented (--non-recursive)" ;
  let cmd = Printf.sprintf " %S -o %S" path out_path in
  [%trace 1 "Running: abella%s" cmd] ;
  if Sys.command (Sys.executable_name ^ cmd) <> 0 then
    failwithf "Could not create %S" thc_path

let load ~compile_source spec ~modname =
  let path = modname ^ spec.suffix in
  let module Src = (val Source.read_compiled
      ~suffix:spec.suffix ~compiled_suffix:spec.compiled_suffix path) in
  let recursive_invoke () =
    recompile ~path:Src.path ~out_path:Src.out_path ~thc_path:Src.thc_path
  in
  let use_artifact = match !Driver_setup.import_mode with
    | `thc -> true
    | `source -> false
    | `auto -> Source.is_thc_trusted Src.thc_path
  in
  let decode bytes =
    let (_digest, _version, art) = read_header_and_body spec bytes in
    art
  in
  if not use_artifact then
    decode (compile_source spec ~modname)
  else begin
    if Src.is_stale then begin
      if Source.virtual_exists Src.path then
        ignore (compile_source spec ~modname)
      else
        recursive_invoke ()
    end ;
    let bytes = Src.thc_contents () in
    let (digest, version, _) = read_header_and_body spec bytes in
    if not !Driver_setup.trust_compiled &&
       digest <> Lazy.force Version.self_digest then begin
      Output.msg_format
        ("@[<v2>Warning: The following %s file was compiled with a "
         ^^ "different version (%s) of Abella; recompiling@,%s@]")
        spec.compiled_suffix version (modname ^ spec.compiled_suffix) ;
      let bytes =
        if Source.virtual_exists Src.path then
          compile_source spec ~modname
        else begin
          recursive_invoke () ;
          Src.thc_contents ()
        end
      in
      decode bytes
    end else
      decode bytes
  end

let add_lemma ?(fin=Finished) name tys thm =
  match Prover.add_lemma ~fin name tys thm with
  | `replace ->
      Output.msg_printf "Warning: overriding existing lemma named %S." name
  | _ -> ()

let update_subordination_ty ty =
  sr := Subordination.update !sr ty

let update_subordination_metaterm mt =
  ignore begin
    Metaterm.map_on_tys (fun ty -> update_subordination_ty ty ; ty) mt
  end

let install_compiled_decl ?strat_errors ?(subordinate=false) decl =
  match decl with
  | CTheorem (name, tys, stmt, fin) ->
      if subordinate then update_subordination_metaterm stmt ;
      if fin = Axiomatic then
        Driver_setup.axioms := name :: !Driver_setup.axioms ;
      add_lemma ~fin name tys stmt
  | CDefine (flavor, typarams, idtys, clauses) ->
      Checks.check_noredef (List.map fst idtys) ;
      if subordinate then begin
        List.iter (fun (_, ty) -> update_subordination_ty ty) idtys ;
        List.iter begin fun cl ->
          update_subordination_metaterm cl.head ;
          update_subordination_metaterm cl.body
        end clauses ;
        Checks.ensure_no_schm_clauses typarams clauses
      end ;
      let (basics, consts) = !sign in
      let consts =
        List.map (fun (id, ty) -> (id, Poly (typarams, ty))) idtys @ consts
      in
      sign := (basics, consts) ;
      Prover.add_defs ?strat_errors typarams idtys flavor clauses
  | CKind (ids, knd) ->
      Checks.check_noredef ids ;
      Prover.add_global_types ids knd
  | CType (ids, typarams, ty)
  | CDeclPred (ids, typarams, ty) ->
      Checks.check_noredef ids ;
      Prover.add_global_consts ~typarams
        (List.map (fun id -> (id, ty)) ids)
  | CImport _
  | CClose _
  | CSuspend _ ->
      failwith "Unexpected declaration in compiled content"

(* Constants that can have reasoning clauses: the pervasive member
   predicate and specification-level (o-valued) constants are excluded. *)
let predicates (_ktable, ctable) =
  ctable |>
  List.filter_map begin fun (id, Poly (_, Ty (_, targty))) ->
    if List.mem id [k_member] || targty = oaty then None
    else Some id
  end
