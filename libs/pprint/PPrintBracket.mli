(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2013  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Minimal bracketing based on precedence and associativity *)

open PPrintEngine

(** Document expressions *)
type docexp =
  | Atom    of document
  (** Atomic expression -- no bracketing needed *)
  | Wrap    of wrapping * document * docexp * document
  (** [Wrap (w, l, de, r)] is [de] delimited by [l] and [r] *)
  | Appl    of int * docappl
  (** Operator applications with precedence *)

(** The application of a document operator *)
and docappl =
  | Prefix  of document * docexp        (** [Prefix (op, de)] *)
  | Postfix of docexp * document        (** [Postfix (de, op)] *)
  | Infix   of document * associativity * docexp list
  (** [Infix (op, asc, des)]; invariant: [List.length des >= 2] *)

(** Associativity for infix applications *)
and associativity = Left | Right | Non

(** Wrapping mode. An [Opaque] wrapping makes the entire wrapped
    document expression behave like an atom; it is used when the
    delimiters are themselves bracket-like. A [Transp]arent wrapping
    is used when the delimiters are not compartmentalizing; for
    example, they might just alter the font or colours without
    printing any text. *)
and wrapping = Opaque | Transp

(** [bracket ~left ~right de] uses [left] and [right] to minimally
    bracket [de] into a document. By default, [left] is [lparen] and
    [right] is [rparen]. *)
val bracket : ?left:document -> ?right:document -> docexp -> document
