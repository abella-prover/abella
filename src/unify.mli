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

type failure =
  | OccursCheck
  | TypesMismatch
  | ConstClash of (Term.term * Term.term)

exception Failure of failure
  
type error =
  | NotLLambda of Term.term

exception Error of error

val right_unify : ?used:Term.id list -> Term.term -> Term.term -> unit
val left_unify : ?used:Term.id list -> Term.term -> Term.term -> unit

val try_with_state : (unit -> bool) -> bool

val try_right_unify : ?used:Term.id list -> Term.term -> Term.term -> bool
val try_left_unify : ?used:Term.id list -> Term.term -> Term.term -> bool  
