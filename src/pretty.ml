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

type 'a printer = ?left:atom -> ?right:atom -> expr -> 'a

let lparen = FUN (fun ff -> pp_print_string ff "(")
let rparen = FUN (fun ff -> pp_print_string ff ")")

let bracket ?(left=lparen) ?(right=rparen) ?(trans=OPAQUE) ?(indent=2) inner =
  Bracket {left; right; indent; inner; trans}

type dom_op = PRE of prec | POST of prec | NOP

let rec reprec de = match de with
  | Atom _ -> (de, NOP)
  | Opapp (prec, Infix (asc, arg1, op, arg2)) ->
      let arg1 = fst (reprec arg1) in
      let arg2 = fst (reprec arg2) in
      (Opapp (prec, Infix (asc, arg1, op, arg2)), NOP)
  | Opapp (prec, Prefix (op, arg)) ->
      let (arg, dom) = reprec arg in
      let prec = match dom with
        | PRE argprec -> min prec argprec
        | _ -> prec
      in
      (Opapp (prec, Prefix (op, arg)), PRE prec)
  | Opapp (prec, Postfix (arg, op)) ->
      let (arg, dom) = reprec arg in
      let prec = match dom with
        | POST argprec -> min prec argprec
        | _ -> prec
      in
      (Opapp (prec, Postfix (arg, op)), POST prec)
  | Bracket br ->
      let (inner, dom) = reprec br.inner in
      let dom = match br.trans with
        | TRANSPARENT -> dom
        | OPAQUE -> NOP
      in
      (Bracket {br with inner}, dom)

let is_prefix = function
  | Opapp (_, Prefix _) -> true
  | _ -> false

let is_postfix = function
  | Opapp (_, Postfix _) -> true
  | _ -> false

let rec is_infix_incompat gpasc myprec myasc = function
  | Opapp (subprec, (Prefix _ | Postfix _))
      when myprec >= subprec ->
      true
  | Opapp (subprec, Infix (subasc, _, _, _))
      when myprec = subprec && not (gpasc = myasc && subasc = myasc) ->
      true
  | Bracket {trans=TRANSPARENT; inner; _} ->
      is_infix_incompat gpasc myprec myasc inner
  | _ -> false

let rec ( >? ) prec ex = match ex with
  | Opapp (subprec, _) when prec > subprec -> true
  | Bracket {trans = TRANSPARENT; inner; _} -> prec >? inner
  | _ -> false

let print_atom ff atm =
  match atm with
  | FMT fmt -> fprintf ff fmt
  | FUN fmt -> fmt ff
  | STR s -> pp_print_string ff s

let rec print ff ?(left=lparen) ?(right=rparen) ex =
  match ex with
  | Atom atm -> print_atom ff atm
  | Bracket br ->
      print_bracket ~left ~right ff br
  | Opapp (prec, appl) -> begin
      match appl with
      | Prefix (op, arg) ->
          (* pp_open_box ff 2 ; begin *)
            print_atom ff op ;
            maybe_enclose
              ~cond:(prec >? arg && not (is_prefix arg))
              ~left ~right ff arg
          (* end ; pp_close_box ff () *)
      | Postfix (arg, op) ->
          (* pp_open_box ff 2 ; begin *)
            maybe_enclose
              ~cond:(prec >? arg && not (is_postfix arg))
              ~left ~right ff arg ;
            print_atom ff op ;
          (* end ; pp_close_box ff () *)
      | Infix (asc, arg1, op, arg2) ->
          (* pp_open_box ff 2 ; begin *)
            maybe_enclose
              ~cond:(prec >? arg1
                     || is_infix_incompat LEFT prec asc arg1)
              ~left ~right ff arg1 ;
            print_atom  ff op ;
            maybe_enclose
              ~cond:(prec >? arg2
                     || is_infix_incompat RIGHT prec asc arg2)
              ~left ~right ff arg2
          (* end ; pp_close_box ff () *)
    end

and maybe_enclose ~cond ~left ~right ff ex =
  if cond then begin
    pp_open_box ff 3 ; begin
      print_atom ff left ;
      print ~left ~right ff ex ;
      print_atom ff right ;
    end ; pp_close_box ff () ;
  end else
    print ~left ~right ff ex

and print_bracket ~left ~right ff br =
  pp_open_box ff br.indent ; begin
    print_atom ff br.left ;
    print ~left ~right ff br.inner ;
    print_atom ff br.right ;
  end ; pp_close_box ff ()

let print ff ?left ?right ex =
  print ff ?left ?right (fst (reprec ex))

let print_string ?(left=lparen) ?(right=rparen) ex =
  let buf = Buffer.create 19 in
  let ff = formatter_of_buffer buf in
  print ~left ~right ff ex ;
  pp_print_flush ff () ;
  Buffer.contents buf


(*
let test () =
  let ff = std_formatter in
  let ei = Opapp (10, Infix (LEFT, Atom (STR "pi"),
                             [STR " ", Opapp (0, Prefix (STR "x\\ ", Atom (STR "x")))])) in
  print ff ei ; pp_print_newline ff () ;
  let ep = Opapp (10, Prefix (STR "pi ", Opapp (0, Prefix (STR "x\\ ", Atom (STR "x"))))) in
  print ff ep ; pp_print_newline ff () ;
  let fi = Opapp (2, Infix (LEFT, ei, [STR " + ", ei])) in
  print ff fi ; pp_print_newline ff () ;
  let fp = Opapp (2, Infix (LEFT, ep, [STR " + ", ep])) in
  print ff fp ; pp_print_newline ff () ;
  pp_print_flush ff ()
*)
