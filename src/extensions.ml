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

let[@inline] curry f (x,y) = f x y
let[@inline] uncurry f x y = f (x,y)

let sorry exn =
  String.concat "\n"
    [ Printexc.to_string exn ; "" ;
      Printexc.get_backtrace () ; "" ;
      "Sorry for displaying a naked OCaml exception. An informative error" ;
      "message has not been designed for this situation." ;
      "To help improve Abella's error messages, please file a bug report at" ;
      "<https://github.com/abella-prover/abella/issues>" ]

let failwithf fmt = Printf.ksprintf failwith fmt

let[@inline] maybe_guard ?guard f =
  match guard with
  | None -> f
  | Some g -> g f

module Format = struct
  include Stdlib.Format

  let pp_print_commaspace ppf () =
    pp_print_string ppf "," ;
    pp_print_space ppf ()
end

module Option = struct
  include Stdlib.Option
  let wrap fn x =
    try Some (fn x) with _ -> None
  let return = some
  let fail = none
  let ( let* ) = bind
  let ( and* ) o1 o2 =
    match o1, o2 with
    | Some x, Some y -> Some (x, y)
    | None, _ | _, None -> None
end

module Result = struct
  include Stdlib.Result
  let wrap fn x =
    try Ok (fn x) with exn -> Error exn
  let wrap2 fn x y =
    try Ok (fn x y) with exn -> Error exn
  let wrap3 fn x y z =
    try Ok (fn x y z) with exn -> Error exn
  let wrap4 fn x y z w =
    try Ok (fn x y z w) with exn -> Error exn
  let return = ok
  exception UnknownError
  let fail = error UnknownError
  let ( let* ) = bind
  let ( and* ) r1 r2 =
    match r1, r2 with
    | Ok x, Ok y -> Ok (x, y)
    | Error e, _
    | _, Error e -> Error e
end

module String = struct
  include Stdlib.String

  let count str char =
    let count = ref 0 in
      String.iter (fun c -> if c = char then incr count) str ;
      !count
end

module List = struct
  include Stdlib.List

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
  include Stdlib.Hashtbl

  let assign dest src =
    clear dest ;
    iter (fun a b -> add dest a b) src

end

(* let memoize fn = *)
(*   let memo = Hashtbl.create 3 in *)
(*   fun x -> *)
(*     try Hashtbl.find memo x *)
(*     with Not_found -> *)
(*       let res = fn x in *)
(*       Hashtbl.add memo x res ; *)
(*       res *)

module IntMap = Stdlib.Map.Make(Stdlib.Int)

module Json = Yojson.Safe

type pos = Lexing.position * Lexing.position
let ghost_pos : pos = (Lexing.dummy_pos, Lexing.dummy_pos)
type 'a wpos = { el : 'a ; pos : pos }
let ghost e = { el = e ; pos = ghost_pos }
let get_el (wp : _ wpos) = wp.el

let string_of_position ((start, stop) : pos) =
  if start == Lexing.dummy_pos then "Unknown position"
  else if start.pos_lnum = stop.pos_lnum then
    Printf.sprintf "File %S, line %d, characters %d-%d"
      start.pos_fname start.pos_lnum
      (start.pos_cnum - start.pos_bol + 1)
      (stop.pos_cnum - stop.pos_bol + 1)
  else
    Printf.sprintf "File %S, line %d, character %d to line %d, character %d"
      start.pos_fname
      start.pos_lnum (start.pos_cnum - start.pos_bol + 1)
      stop.pos_lnum (stop.pos_cnum - stop.pos_bol + 1)

let failwithf_at ~pos fmt =
  if pos == ghost_pos || fst pos == Lexing.dummy_pos then
    failwithf fmt
  else
    failwithf ("%s\n" ^^ fmt) (string_of_position pos)

let json_of_position (lft, rgt : pos) : Json.t =
  let open Lexing in
  if ( lft = Lexing.dummy_pos
       || lft.pos_fname = ""
       || lft.pos_fname <> rgt.pos_fname )
  then `Null else
    `List [
      `Int lft.pos_cnum ;
      `Int lft.pos_bol ;
      `Int lft.pos_lnum ;
      `Int rgt.pos_cnum ;
      `Int rgt.pos_bol ;
      `Int rgt.pos_lnum ;
    ]

let lexbuf_from_file filename =
  match Lexing.from_channel (open_in_bin filename) with
  | lexbuf ->
      lexbuf.Lexing.lex_curr_p <- {
        lexbuf.Lexing.lex_curr_p with
        Lexing.pos_fname = filename } ;
      lexbuf
  | exception Sys_error msg ->
      failwithf "Failure reading %S: %s" filename msg

module Filename = struct
  include Stdlib.Filename

  let split =
    let rec elems bases fn =
      match fn with
      | "" -> bases
      | _ -> begin
          let bases = basename fn :: bases in
          match dirname fn with
          | "." -> bases
          | fn ->
              if fn = Filename.dir_sep then bases
              else (elems[@tailcall]) bases fn
        end
    in
    let[@tail_mod_cons] rec collapse stack elems =
      match elems with
      | [] -> List.rev stack
      | x :: elems -> begin
          match x with
          | "." -> collapse stack elems
          | ".." -> begin
              match stack with
              | [] -> ".." :: collapse [] elems
              | _ :: stack -> collapse stack elems
            end
          | _ -> collapse (x :: stack) elems
        end
    in
    let at_least_dot = function
      | [] -> ["."]
      | l -> l
    in
    fun fn -> fn |> elems [] |> collapse [] |> at_least_dot

  let clean ?(sep=Filename.dir_sep) fn =
    String.concat sep (split fn)
end

module Xdg = struct
  open struct
    let ensure_dir dir =
      if Sys.file_exists dir then
        if Sys.is_directory dir then ()
        else [%bug] "Not a directory: %s" dir
      else Sys.mkdir dir 0o755

    let ( / ) parent child =
      ensure_dir parent ;
      let child = Filename.concat parent child in
      ensure_dir child ;
      child

    let abella = "abella"

    let home =
      Sys.getenv_opt (if Sys.win32 then "USERPROFILE" else "HOME") |>
      Option.value ~default:""
    let xdg_cache_dir =
      Sys.getenv_opt "XDG_CACHE_HOME" |>
      Option.value ~default:(home / ".cache")
    let xdg_config_dir =
      Sys.getenv_opt "XDG_CONFIG_HOME" |>
      Option.value ~default:(home / ".config")
    let xdg_state_dir =
      Sys.getenv_opt "XDG_STATE_HOME" |>
      Option.value ~default:(home / ".local" / "state")
  end

  let cache_dir   = xdg_cache_dir  / abella / "run"
  let config_dir  = xdg_config_dir / abella
  let state_dir   = xdg_state_dir  / abella
end
