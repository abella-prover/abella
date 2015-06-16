(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

val rref      : 'a -> 'a ref
val table     : unit -> ('a, 'b) Hashtbl.t
val primitive : copy:('a -> 'b) -> assign:('a -> 'b -> unit) -> 'a -> 'a

type state

val snapshot : unit -> state
val reload   : state -> unit
val reset    : unit -> unit

module Undo : sig
  val reset : unit -> unit
  val undo  : unit -> unit
  val push  : unit -> unit
  val back  : int -> unit

  val set_enabled : bool -> unit
end
