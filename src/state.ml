(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015-2022  Inria (Institut National de Recherche
 *                                 en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions

type cell = unit -> unit
type snap = cell list

let __snappers : (unit -> unit -> unit) list ref = ref []

(* Restore cells for the values at registration. These hold the initial
   values strongly, unlike snapshot cells, so that a pristine session can
   be reconstructed after imports have changed the global state. *)
let __initial_snappers : (unit -> unit) list ref = ref []

exception Killme

let rref x =
  let xr = ref x in
  let wx = Weak.create 1 in
  Weak.set wx 0 (Some xr) ;
  let snap () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some xr ->
        let y = !xr in
        fun () -> xr := y
  in
  let initial () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some xr -> xr := x
  in
  __snappers := snap :: !__snappers ;
  __initial_snappers := initial :: !__initial_snappers ;
  xr

let table ?initial () =
  let ht = match initial with Some tab -> tab | None -> Hashtbl.create 19 in
  let wx = Weak.create 1 in
  Weak.set wx 0 (Some ht) ;
  let snap () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some ht ->
        let saved = Hashtbl.copy ht in
        fun () -> Hashtbl.assign ht saved
  in
  let initial = Hashtbl.copy ht in
  let reset () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some ht -> Hashtbl.assign ht initial
  in
  __snappers := snap :: !__snappers ;
  __initial_snappers := reset :: !__initial_snappers ;
  ht

let make ~copy ~assign x =
  let wx = Weak.create 1 in
  Weak.set wx 0 (Some x) ;
  let snap () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some x ->
        let saved = copy x in
        fun () -> assign x saved
  in
  let initial = copy x in
  let reset () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some x -> assign x initial
  in
  __snappers := snap :: !__snappers ;
  __initial_snappers := reset :: !__initial_snappers ;
  x

let snapshot () : snap =
  let (snap, snappers) = List.fold_left begin fun (snap, snappers) next ->
    try ((next () :: snap), (next :: snappers)) with
    | Killme -> (snap, snappers)
  end ([], []) !__snappers in
  __snappers := snappers ;
  snap

let reload (snap : snap) = List.iter (fun f -> f ()) snap

let reset () =
  __initial_snappers :=
    List.filter begin fun restore ->
      try restore () ; true with
      | Killme -> false
    end !__initial_snappers

module Undo = struct
  let enabled = ref true

  let set_enabled en =
    (* Printf.eprintf "Undos are %senabled.\n%!" (if en then "" else "NOT ") ; *)
    enabled := en

  let is_enabled () = !enabled

  let stack : snap list ref = ref []

  let describe _msg =
    (* Printf.eprintf "AFTER(%s) : %d\n%!" msg (List.length !stack) ; *)
    ()

  let reset () =
    stack := [] ;
    describe "reset"

  let undo () =
    if !enabled then begin
      match !stack with
      | [] -> failwith "Nothing left to undo"
      | prev :: older ->
          reload prev ;
          stack := older ;
          describe "undo"
    end

  let push () =
    if !enabled then begin
      stack := snapshot () :: !stack ;
      describe "push"
    end

  let back n0 =
    if !enabled then begin
      let rec spin hist n =
        match hist, n with
        | (here :: hist), 1 ->
            reload here ;
            stack := hist ;
            describe ("back " ^ string_of_int n0)
        | (_ :: hist), n ->
            spin hist (n - 1)
        | [], _ ->
            failwith "Cannot go that far back!"
      in
      spin !stack n0
    end
end
