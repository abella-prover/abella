(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006 Nadathur, Linnell, Baelde, Ziegler                    *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

type tag = Eigen | Constant | Logic
type id = string
type var = {
  name : id ;
  tag  : tag    ;
  ts   : int
}

(* Terms. The use of references allow in-place normalization,
 * but is completely hidden by the interface. *)

type term
type ptr
type envitem = Dum of int | Binding of term * int
type env = envitem list

type rawterm = 
  | Var of var
  | DB of int
  | Lam of int * term
  | App of term * term list
  | Susp of term * int * int * env
  | Ptr of ptr (* Sorry about this one, hiding it is costly.. *)

(* [observe t] is the way to analyze the structure of a term. *)
val observe : term -> rawterm

(** Creation of terms.
  * There is probably more to come here. *)

(* Two const/var/atoms created with the same names are shared except if
 * reset_namespace is called between the two creations. *)
val reset_namespace : unit -> unit
val reset_namespace_vars : unit -> unit

val const : ?tag:tag -> string -> int -> term
val var : ?tag:tag -> string -> int -> term

val string : string -> term

val binop : string -> term -> term -> term

val collapse_lam : term -> term

val app : term -> term list -> term
val susp : term -> int -> int -> env -> term
val db : int -> term

module Notations :
sig
  val (%=) : term -> term -> bool
  val (!!) : term -> rawterm
  val (//) : int -> term -> term
  val (^^) : term -> term list -> term
end

exception NotValidTerm

(* Fast structural equality modulo Ptr.
 * Fast: try to use physical equality first.
 * Structural: no normalization peformed. *)
val eq : term -> term -> bool

(* Binding a variable to a term. The *contents* of the cell representing the
 * variable is a reference which must be updated. Also the variable must
 * not be made a reference to itself. This can be changed to mimic the
 * Prolog representation of bound variables but then deref will have to
 * work differently. This is the place to introduce trailing.
 * David: What's trailing ? *)

type bind_state
type subst
val save_state : unit -> bind_state
val restore_state : bind_state -> unit
val get_subst : bind_state -> subst
val where : unit -> unit

val bind : term -> term -> unit

(* Raise the substitution *)
val add_dummies : env -> int -> int -> env

(* Add [n] abstractions. *)
val lambda : int -> term -> term

val getAbsName : unit -> string

exception NonNormalTerm

(** Abstract [t] over term [v]. *)
val abstract_var : term -> term -> term

(** Abstract [t] over constant or variable named [id]. *)
val abstract : string -> term -> term

(** Logic variables of [ts]. *)
val logic_vars : term list -> term list

(** LPP specific additions and changes *)
val atom : ?tag:tag -> ?ts:int -> string -> term
val fresh : ?tag:tag -> int -> term
val fresh_wrt : tag -> id -> id list -> term * id list 
  
val find_vars : tag -> term list -> var list
val map_vars : (var -> 'a) -> term -> 'a list
val map_vars_list : (var -> 'a) -> term list -> 'a list
  
val apply_subst : subst -> unit
  
val reset_namespace_except : id list -> unit
