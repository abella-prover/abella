(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
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

open Extensions

type 'a t = ('a * 'a) list

let empty = []

let add_arc arcs a b =
  if List.mem (a, b) arcs then arcs else (a, b)::arcs

let direct_predecessors arcs a =
  a :: (List.map fst (List.filter (snd >> (=) a) arcs))

let predecessors arcs a =
  let rec aux acc a =
    if List.mem a acc then
      acc
    else
      List.fold_left aux (a::acc) (direct_predecessors arcs a)
  in
    aux [] a

let is_path arcs a b =
  List.mem a (predecessors arcs b)
