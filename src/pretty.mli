(* Pretty printing framework
 *
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014-2022  Inria (Institut National de Recherche
 *                          en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Simple declarative framework for pretty printing

    Internally, this uses {!Format} from the standard library *)

open Format

type prec   = int
type trans  = OPAQUE | TRANSPARENT
type assoc  = LEFT | RIGHT | NON

type atom =
  | FMT of (unit, formatter, unit) format
  | FUN of (formatter -> unit)
  | STR of string

type expr =
  | Atom    of atom
  | Bracket of bracketing
  | Opapp   of prec * opapp

and bracketing = {
  left  : atom ;
  right : atom ;
  indent : int ;
  inner : expr ;
  trans : trans ;
}

and opapp =
  | Prefix  of atom * expr
  | Postfix of expr * atom
  | Infix   of assoc * expr * atom * expr

val bracket : ?left:atom -> ?right:atom -> ?trans:trans -> ?indent:int -> expr -> expr

type 'a printer = ?left:atom -> ?right:atom -> expr -> 'a

val print        : formatter -> unit printer
val print_string : string printer
