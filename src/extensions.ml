(****************************************************************************)
(* Copyright (C) 2007-2008 Gacek                                            *)
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

let (>>) f g x = g (f x)
let (|>) x f = f x

let curry f (x,y) = f x y
let uncurry f x y = f (x,y)  

module Option = struct
  let is_some x =
    match x with
      | Some _ -> true
      | None -> false

  let is_none x =
    match x with
      | Some _ -> false
      | None -> true

  let get x =
    match x with
      | Some v -> v
      | None -> failwith "Option.get called on None"

  let map_default f default x =
    match x with
      | Some v -> f v
      | None -> default
end

module List = struct
  include List
    
  let mem ?(cmp=(=)) elt list =
    let rec aux list =
      match list with
        | [] -> false
        | head::tail -> cmp elt head || aux tail
    in
      aux list

  let remove ?(cmp=(=)) elt list =
    let rec aux list =
      match list with
        | [] -> []
        | head::tail when cmp elt head -> aux tail
        | head::tail -> head::(aux tail)
    in
      aux list

  let unique ?(cmp=(=)) list =
    let rec aux list =
      match list with
        | [] -> []
        | head::tail -> head::(aux (remove ~cmp:cmp head tail))
    in
      aux list

  let find_duplicate list =
    let rec aux list =
      match list with
        | [] -> None
        | head::tail when mem head tail -> Some head
        | _::tail -> aux tail
    in
      aux list
        
  let find_all f list =
    filter f list

  let find_some f list =
    let rec aux list =
      match list with
        | [] -> failwith "Found none"
        | head::tail ->
            match f head with
              | Some v -> v
              | None -> aux tail
    in
      aux list

  let filter_map f list =
    map Option.get (find_all Option.is_some (map f list))

  let flatten_map f list =
    flatten (map f list)

  let remove_all f list =
    find_all (fun x -> not (f x)) list

  let minus list1 list2 =
    remove_all (fun e -> mem e list2) list1

  let rec take n list =
    match list, n with
      | [], _ -> []
      | _, n when n <= 0 -> []
      | x::xs, n -> x::(take (n-1) xs)

  let remove_assocs to_remove alist =
    let rec aux alist =
      match alist with
        | (a, b)::rest ->
            if mem a to_remove
            then aux rest
            else (a, b)::(aux rest)
        | [] -> []
    in
      aux alist

  let assoc_all ?(cmp=(=)) x list =
    let rec aux list =
      match list with
        | [] -> []
        | (a, b)::tail when cmp x a -> b::(aux tail)
        | _::tail -> aux tail
    in
      aux list

  let remove_all_assoc ?(cmp=(=)) x list =
    let rec aux list =
      match list with
        | [] -> []
        | (a, b)::tail when cmp x a -> aux tail
        | head::tail -> head::(aux tail)
    in
      aux list

  let max list =
    let rec aux list m =
      match list with
        | [] -> m
        | head::tail -> aux tail (max head m)
    in
      aux list 0

  let rec distribute elt list =
    match list with
      | [] -> [[elt]]
      | head::tail -> (elt::list) ::
          (map (fun x -> head::x) (distribute elt tail))

  (* Generate all permutations of all n element subsets of list *)
  let rec permute n list =
    if n = 0 then
      [[]]
    else
      match list with
        | [] -> []
        | head::tail ->
            (flatten_map (distribute head) (permute (n-1) tail))
            @ (permute n tail)


  let rec range a b =
    if a > b then
      []
    else
      a :: range (a+1) b
end

