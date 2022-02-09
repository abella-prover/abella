(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2022 Inria (Institut National de Recherche            *)
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

let (>>) f g x = g (f x)
let (|>) x f = f x

let curry f (x,y) = f x y
let uncurry f x y = f (x,y)

let bugf      fmt = Printf.ksprintf (fun s -> Printf.eprintf "%s\n%!" s ; failwith "Bug")
    ("[ABELLA BUG]\n" ^^ fmt ^^
     "\nPlease report this at https://github.com/abella-prover/abella/issues")

type provenance =
  | Unknown
  | Stdin
  | Position of Lexing.position
  | Range of Lexing.position * Lexing.position

let provenance_to_string prov =
  let open Lexing in
  match prov with
  | Unknown -> "Unknown provenance:\n"
  | Stdin -> "Standard input:\n"
  | Position pos ->
      Printf.sprintf
        "File %S, line %d, character %d:\n"
        pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
  | Range (posl, posr) when posl.pos_fname = posr.pos_fname ->
      if posl.pos_lnum <> posr.pos_lnum then
        Printf.sprintf
          "File %S, lines %d-%d:\n"
          posl.pos_fname posl.pos_lnum posr.pos_lnum
      else
        Printf.sprintf
          "File %S, line %d, characters %d-%d:\n"
          posl.pos_fname posl.pos_lnum
          (posl.pos_cnum - posl.pos_bol)
          (posr.pos_cnum - posr.pos_bol)
  | Range (posl, posr) ->
      bugf "output_provenance: %S != %S" posl.pos_fname posr.pos_fname

let failwithf fmt = Printf.ksprintf failwith fmt
let maybe_guard ?guard f =
  match guard with
  | None -> f
  | Some g -> g f

let pp_print_commaspace ff () =
    Format.pp_print_string ff "," ;
    Format.pp_print_space ff ()

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

  let default default x =
    match x with
      | Some v -> v
      | None -> default
end

module String = struct
  include String

  let count str char =
    let count = ref 0 in
      String.iter (fun c -> if c = char then incr count) str ;
      !count

  let split ?test ?(start = 0) ?len str =
    let test = match test with
      | None -> begin function
        | ' ' | '\t' | '\n' | '\r' -> true
        | _ -> false
        end
      | Some test -> test
    in
    let strlen = String.length str in
    let len = match len with
      | None -> strlen
      | Some len -> len
    in
    if start < 0 || len < 0 || (start + len) > String.length str then
      invalid_arg "String.split" ;
    let toks = ref [] in
    let emit tstart tend =
      let tok = String.sub str tstart (tend - tstart) in
      if tok <> "" then toks := tok :: !toks
    in
    let rec spin tstart cur =
      if cur >= start + len then emit tstart cur else
      if test str.[cur] then begin
        emit tstart cur ;
        let cur = cur + 1 in
        spin cur cur
      end else spin tstart (cur + 1)
    in
    spin start start ;
    List.rev !toks
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

  let is_unique ?(cmp=(=)) list =
    let rec aux list =
      match list with
        | [] -> true
        | head::tail -> not (mem ~cmp head tail) && aux tail
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

  let map ?guard f list = map (maybe_guard ?guard f) list

  let iter ?guard f list = iter (maybe_guard ?guard f) list

  let iteri ?guard f list =
    let f = maybe_guard ?guard f in
    let rec spin n = function
      | [] -> ()
      | x :: xs -> f n x ; spin (n + 1) xs
    in
    spin 0 list

  let iter_sep ~sep f list =
    let rec spin0 = function
      | [] -> ()
      | [x] -> f x
      | x :: xs -> f x ; spin1 xs
    and spin1 = function
      | [] -> ()
      | x :: xs -> sep () ; f x ; spin1 xs
    in
    spin0 list

  let find_all ?guard f list =
    filter (maybe_guard ?guard f) list

  let find_some ?guard f list =
    let f = maybe_guard ?guard f in
    let rec aux list =
      match list with
        | [] -> None
        | head::tail ->
            match f head with
              | Some v -> Some v
              | None -> aux tail
    in
      aux list

  let filter_map ?guard f list =
    let f = maybe_guard ?guard f in
    map Option.get (find_all Option.is_some (map f list))

  let flatten_map ?guard f list =
    let f = maybe_guard ?guard f in
    flatten (map f list)

  let remove_all ?guard f list =
    let f = maybe_guard ?guard f in
    find_all (fun x -> not (f x)) list

  let minus ?(cmp=(=)) list1 list2 =
    remove_all (fun e -> mem ~cmp e list2) list1

  let intersect ?(cmp=(=)) list1 list2 =
    find_all (fun e -> mem ~cmp e list2) list1

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
        | (a, _b)::tail when cmp x a -> aux tail
        | head::tail -> head::(aux tail)
    in
      aux list

  let collate_assoc ?(cmp=(=)) alist =
    let rec spin finished ck cv = function
      | [] -> List.rev ((ck, List.rev cv) :: finished)
      | (nk, nv) :: rest ->
        if cmp ck nk
        then spin finished ck (nv :: cv) rest
        else spin ((ck, List.rev cv) :: finished) nk [nv] rest
    in
    match alist with
    | [] -> []
    | (nk, nv) :: rest -> spin [] nk [nv] rest

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

  (* Generate all n element subsets of list *)
  let rec choose n list =
    if n = 0 then
      [[]]
    else
      match list with
        | [] -> []
        | head::tail ->
            (map (fun t -> head::t) (choose (n-1) tail))
            @ (choose n tail)

  let rec range a b =
    if a > b then
      []
    else
      a :: range (a+1) b

  let number list =
    let rec aux i list =
      match list with
        | [] -> []
        | head::tail -> (i, head) :: (aux (i+1) tail)
    in
      aux 1 list

  let fold_left1 f list =
    match list with
      | x::xs -> fold_left f x xs
      | _ -> invalid_arg "Empty list"

  let rec drop n list =
    match list with
      | _x::xs when n > 0 -> drop (n-1) xs
      | _ -> list

  let drop_last n list = rev (drop n (rev list))
  let take_last n list = rev (take n (rev list))

  let rec last = function
    | [] -> invalid_arg "List.last"
    | [x] -> x
    | _ :: l -> last l

  let rev_map f list =
    let rec aux list acc =
      match list with
        | [] -> acc
        | x::xs -> aux xs (f x :: acc)
    in
      aux list []

  let rec rev_app xs ys =
    match xs with
      | [] -> ys
      | x::xs -> rev_app xs (x::ys)

  let replicate n x =
    let rec aux = function
      | 0 -> []
      | i -> x :: aux (i-1)
    in
      aux n

  let map_fst f list =
    map (fun (x,y) -> (f x, y)) list

  let map_snd f list =
    map (fun (x,y) -> (x, f y)) list

  let rec combine3 l1 l2 l3 =
    match l1, l2, l3 with
      | [], [], [] -> []
      | x::xs, y::ys, z::zs -> (x, y, z) :: (combine3 xs ys zs)
      | _ -> raise (Invalid_argument "List.combine3")

end

module Hashtbl = struct
  include Hashtbl

  let assign dest src =
    clear dest ;
    iter (fun a b -> add dest a b) src

end

let memoize fn =
  let memo = Hashtbl.create 3 in
  fun x ->
    try Hashtbl.find memo x with Not_found ->
      let res = fn x in
      Hashtbl.add memo x res ;
      res


module Either = struct
  type ('a, 'b) either = Left of 'a | Right of 'b

  let either left right e =
    match e with
      | Left x -> left x
      | Right x -> right x

  let partition_eithers eithers =
    let left x (l, r) = (x::l, r) in
    let right x (l, r) = (l, x::r) in
      List.fold_right (either left right) eithers ([], [])
end

module IntMap : Map.S with type key := int =
  Map.Make (struct
    type t = int
    let compare (x : int) y =
      if x < y then -1 else
      if x = y then 0 else 1
  end)
