(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026 Inria (Institut National de Recherche
 *                            en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Path helpers for the project handoff that abella_doc embeds in each
   theorem page. *)

(* This is a library so that it can be tested. Lots of finicky
   details to get right *)

let split_path path = String.split_on_char '/' path

let normalize_parts parts =
  let rec loop acc = function
  | [] -> List.rev acc
  | ("" | ".") :: rest -> loop acc rest
  | ".." :: rest ->
      (match acc with
       | [] | ".." :: _ -> loop (".." :: acc) rest
       | _ :: acc' -> loop acc' rest)
  | part :: rest -> loop (part :: acc) rest
  in
  loop [] parts

let relative_path ~from ~target =
  let src = normalize_parts (split_path from) in
  let dst = normalize_parts (split_path target) in
  let rec common left right =
    match left, right with
    | x :: left' , y :: right' when x = y -> common left' right'
    | _ -> (left, right)
  in
  let (src, dst) = common src dst in
  let ups = List.map (fun _ -> "..") src in
  match ups @ dst with
  | [] -> "."
  | parts -> String.concat "/" parts
