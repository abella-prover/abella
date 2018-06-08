(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015-2018  Inria (Institut National de Recherche
 *                          en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

val rref      : 'a -> 'a ref
val table     : unit -> ('a, 'b) Hashtbl.t
val make      : copy:('a -> 'b) -> assign:('a -> 'b -> unit) -> 'a -> 'a

type snap
val snapshot : unit -> snap
val reload   : snap -> unit

module Undo : sig
  val reset : unit -> unit
  val undo  : unit -> unit
  val push  : unit -> unit
  val back  : int -> unit

  val set_enabled : bool -> unit
end
