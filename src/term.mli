(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006-2009 Nadathur, Linnell, Baelde, Ziegler, Gacek        *)
(* Copyright (C) 2013-2016 Inria (Institut National de Recherche            *)
(*                         en Informatique et en Automatique)               *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

(* Kinds *)
type knd = Knd of int

val kind : int -> knd
val kincr : knd -> knd
val karity : knd -> int

(* Types *)

type aty = AtmTy of string * ty list
and  ty = Ty of ty list * aty

val atybase : string -> aty
val atyapp : aty -> ty -> aty

val tyarrow : ty list -> ty -> ty
val tybase : aty -> ty
val oty : ty
val olistty : ty
val propty : ty

(* Variables *)

type tag = Eigen | Constant | Logic | Nominal
type id = string

module Itab : Map.S with type key := id
module Iset : sig
    include Set.S with type elt := id
    val of_list : id list -> t
  end

type var = private {
  name : id ;
  tag  : tag ;
  ts   : int ;
  ty   : ty ;
}

(* Terms. The use of references allow in-place normalization,
 * but is completely hidden by the interface. *)

type ptr
type tyctx = (id * ty) list

type term = private
  | Var of var
  | DB of int
  | Lam of tyctx * term
  | App of term * term list
  | Susp of term * int * int * env
  | Ptr of ptr (* Sorry about this one, hiding it is costly.. *)
and envitem = Dum of int | Binding of term * int
and env = envitem list

(* [observe t] is the way to analyze the structure of a term. *)
val observe : term -> term

(** [deep_copy t] copies the term t by duplicating all variables *)
val deep_copy : term -> term

(** Creation of terms.
  * There is probably more to come here. *)

val var : tag -> string -> int -> ty -> term

val app : term -> term list -> term
val susp : term -> int -> int -> env -> term
val db : int -> term

module Notations :
sig
  val (//) : tyctx -> term -> term
  val (^^) : term -> term list -> term
end

(* get a list of tys from a type context *)
val get_ctx_tys : tyctx -> ty list

val eq : term -> term -> bool

(* Binding a variable to a term. The *contents* of the cell representing the
 * variable is a reference which must be updated. Also the variable must
 * not be made a reference to itself. *)

val bind : term -> term -> unit

type bind_state
val get_bind_state : unit -> bind_state
val set_bind_state : bind_state -> unit

(* Scoped bind state is more efficient than regular bind state, but it
   must always be used in a lexically scoped fashion. The unwind_state
   wraps a function with a scoped get and set. *)

type scoped_bind_state
val get_scoped_bind_state : unit -> scoped_bind_state
val set_scoped_bind_state : scoped_bind_state -> unit

val unwind_state : ('a -> 'b) -> ('a -> 'b)

(* Raise the substitution *)
val add_dummies : env -> int -> int -> env

(* Add abstractions. *)
val lambda : tyctx -> term -> term

(** Abstract [t] over constant or variable named [id]. *)
val abstract : string -> ty -> term -> term

(** Abella specific additions and changes *)
val const : ?ts:int -> string -> ty -> term
val fresh : ?tag:tag -> int -> ty -> term
val fresh_wrt : ts:int -> tag -> id -> ty ->
                  (id * term) list -> term * (id * term) list

val nominal_var : string -> ty -> term

val find_vars : tag -> term list -> var list
val find_var_refs : tag -> term list -> term list
val map_vars : (var -> 'a) -> term list -> 'a list

val term_to_var : term -> var
val term_to_name : term -> string
val term_to_pair : term -> string * term

val has_logic_head : term -> bool
val has_eigen_head : term -> bool

val hnorm : term -> term
val norm : term -> term

val pretty_ty : ty -> Pretty.expr
val format_ty : Format.formatter -> ty -> unit
val ty_to_string : ty -> string
val aty_to_string : aty -> string
val knd_to_string : knd -> string


val var_to_string : var -> string

class type term_printer = object
  method print : tyctx -> term -> Pretty.expr
end
val core_printer : term_printer
val default_printer : term_printer ref

val format_term :  ?printer:term_printer -> ?cx:tyctx ->
  Format.formatter -> term -> unit
val term_to_string : ?printer:term_printer -> ?cx:tyctx ->
  term -> string

val prefix : tag -> string

val get_used : term list -> (id * term) list
val is_free : term -> bool

val is_nominal_name : string -> bool
val is_nominal : term -> bool
val fresh_name : string -> (string * 'a) list -> string
val term_head : term -> (term * term list) option
val is_head_name : string -> term -> bool
val term_head_name : term -> string

val is_capital_name : string -> bool
val capital_tids : term list -> (id * ty) list
val question_tids : term list -> (id * ty) list
val nominal_tids : term list -> (id * ty) list
val all_tids : term list -> (id * ty) list

val iter_term_tys : (ty -> unit) -> term -> unit
(* val map_on_term_tys : (ty -> ty) -> term -> term *)

val tc : tyctx -> term -> ty

val tyvar : string -> ty
val is_tyvar : string -> bool
val is_gen_tyvar : string -> bool
val fresh_tyvar : unit -> ty
val name_of_gen_tyvar : string -> string
val get_tyvars : ty -> string list
val get_term_tyvars : term -> string list

val mark_gen_tyvar : string list -> ty -> ty
val tag_gen_tyvar : string -> string

val get_tycstr : (string -> bool) -> ty -> string list

val contains_tyvar : ty -> bool 
val contains_gen_tyvar : ty -> bool
val term_contains_tyvar : term -> bool
val term_contains_gen_tyvar : term -> bool
val is_poly_term : term -> bool

(* Type substitutions *)
type tysub = (string * ty) list

val apply_bind_ty : string -> ty -> ty -> ty
val apply_sub_ty : tysub -> ty -> ty
val apply_bind_sub : string -> ty -> tysub -> tysub

val is_ground_tysub : tysub -> bool
val inst_var_ty : tysub -> term -> term
(* val inst_term_ty : tysub -> term -> term *)
val term_fully_instantiated : term -> bool
    
(* Manipulation of clauses *)
val is_imp : term -> bool
val extract_imp : term -> term * term

val is_amp : term -> bool
val extract_amp : term -> term * term

val is_pi : term -> bool
val extract_pi : term -> term
val replace_pi_with_const : term -> tyctx * term

val print_var_tys : term -> unit
val print_ty_sub : tysub -> unit
