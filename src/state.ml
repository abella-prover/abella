(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See COPYING for licensing details.
 *)

open Extensions

type cell = {
  get : unit -> Obj.t ;
  put : Obj.t -> unit ;
  reset : unit -> unit ;
}

let __state : cell list ref = ref []

let rref x =
  let xr = ref x in
  let put x = xr := Obj.obj x in
  let get () = Obj.repr !xr in
  let reset () = xr := x in
  __state := {get ; put ; reset} :: !__state ;
  xr

let table () =
  let ht = Hashtbl.create 19 in
  let get () = Obj.repr (Hashtbl.copy ht) in
  let put x = Hashtbl.assign ht (Obj.obj x) in
  let reset () = Hashtbl.clear ht  in
  __state := {get ; put ; reset} :: !__state ;
  ht

let primitive ~copy ~assign x =
  let orig = copy x in
  let reset () = assign x orig in
  let put y = assign x (Obj.obj y) in
  let get () = Obj.repr (copy x) in
  __state := {get ; put ; reset} :: !__state ;
  x

type state = Obj.t list

let snapshot () : state =
  List.map (fun c -> c.get ()) !__state

let reload (snap : state) =
  try
    List.iter2 (fun c v -> c.put v) !__state snap
  with Invalid_argument _ -> bugf "Cannot reload snapshot!"

let reset () =
  List.iter (fun c -> c.reset ()) !__state

module Undo = struct
  let enabled = ref true

  let set_enabled en = enabled := en

  let stack : state list ref = ref []

  let describe msg =
    ()
    (* Printf.eprintf "AFTER(%s) : %d\n%!" msg (List.length !stack) *)

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
