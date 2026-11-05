(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                            en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Marshalling helpers shared by the .thc and .thmodc artifacts. *)

open Term
open Typing
open Extensions

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

(* Constants that can have reasoning clauses: the pervasive member
   predicate and specification-level (o-valued) constants are excluded. *)
let predicates (_ktable, ctable) =
  ctable |>
  List.filter_map begin fun (id, Poly (_, Ty (_, targty))) ->
    if List.mem id [k_member] || targty = oaty then None
    else Some id
  end
