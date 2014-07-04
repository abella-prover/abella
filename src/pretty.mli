(* Pretty printing framework
 *
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See COPYING for licensing details.
 *)

(** Simple declarative framework for pretty printing

    Internally, this uses {!Format} from the standard library *)

open Format

type fmt = (unit, formatter, unit) format
type prec   = int
type trans  = OPAQUE | TRANSP
type assoc  = LEFT | RIGHT | NON

type expr =
  | Atom    of fmt
  | Bracket of bracketing
  | Opapp   of prec * opapp

and bracketing = {
  left  : fmt ;
  right : fmt ;
  inner : expr ;
  trans : trans ;
}

and opapp =
  | Prefix  of fmt * expr
  | Postfix of expr * fmt
  | Infix   of assoc * expr * (fmt * expr) list

val bracket : ?left:fmt -> ?right:fmt -> ?trans:trans -> expr -> expr

val print : ?left:fmt -> ?right:fmt -> formatter -> expr -> unit
