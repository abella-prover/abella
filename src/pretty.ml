(* Pretty printing framework
 *
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2014  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See COPYING for licensing details.
 *)

(** Simple declarative framework for pretty printing

    Internally, this uses {!Format} from the standard library *)

open Format

type fmt = (unit, formatter, unit) format
type prec   = int
type trans  = OPAQUE | TRANSP
type assoc  = LEFT | RIGHT | NON

type expr =
  | Atom    of fmt
  | Bracket of bracketing
  | Opapp   of prec * opapp

and bracketing = {
  left  : fmt ;
  right : fmt ;
  inner : expr ;
  trans : trans ;
}

and opapp =
  | Prefix  of fmt * expr
  | Postfix of expr * fmt
  | Infix   of assoc * expr * (fmt * expr) list

let lparen : fmt = format_of_string "("
let rparen : fmt = format_of_string ")"

let bracket ?(left=lparen) ?(right=rparen) ?(trans=OPAQUE) inner =
  Bracket {left; right; inner; trans}

type dom_op = PRE of prec |POST of prec | NOP

let rec reprec de = match de with
  | Atom _ -> (de, NOP)
  | Opapp (prec, Infix (asc, arg1, args)) ->
      let arg1 = fst (reprec arg1) in
      let args = List.map (fun (op, arg) -> (op, fst (reprec arg))) args in
      (Opapp (prec, Infix (asc, arg1, args)), NOP)
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
        | TRANSP -> dom
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
  | Opapp (subprec, Infix (subasc, _, _))
      when myprec = subprec && not (gpasc = myasc && subasc = myasc) ->
      true
  | Bracket {trans=TRANSP; inner; _} ->
      is_infix_incompat gpasc myprec myasc inner
  | _ -> false

let rec ( >? ) prec ex = match ex with
  | Opapp (subprec, _) when prec > subprec -> true
  | Bracket {trans = TRANSP; inner; _} -> prec >? inner
  | _ -> false

let rec print ?(left=lparen) ?(right=rparen) ff ex =
  match ex with
  | Atom d -> fprintf ff d
  | Bracket br ->
      kprint_bracket ~left ~right ff br
  | Opapp (prec, appl) -> begin
      match appl with
      | Prefix (op, arg) ->
          pp_open_box ff 2 ; begin
            fprintf ff op ;
            pp_print_space ff () ;
            maybe_enclose
              ~cond:(prec >? arg && not (is_prefix arg))
              ~left ~right ff arg
          end ; pp_close_box ff ()
      | Postfix (arg, op) ->
          pp_open_box ff 2 ; begin
            maybe_enclose
              ~cond:(prec >? arg && not (is_postfix arg))
              ~left ~right ff arg ;
            pp_print_space ff () ;
            fprintf ff op ;
          end ; pp_close_box ff ()
      | Infix (asc, arg1, args) ->
          let (args, (opN, argN)) = match List.rev args with
            | argN :: args -> (List.rev args, argN)
            | _ -> failwith "Pretty.print: Infix needs at least two operands"
          in
          pp_open_box ff 2 ; begin
            maybe_enclose
              ~cond:(prec >? arg1
                    || is_infix_incompat LEFT prec asc arg1)
              ~left ~right ff arg1 ;
            List.iter begin fun (op, arg) ->
              fprintf ff op ; pp_print_cut ff () ;
              maybe_enclose
                ~cond:(prec >? arg)
                ~left ~right ff arg ;
            end args ;
            fprintf ff opN ; pp_print_cut ff () ;
            maybe_enclose
              ~cond:(prec >? argN
                    || is_infix_incompat RIGHT prec asc argN)
              ~left ~right ff argN
          end ; pp_close_box ff ()
    end

and maybe_enclose ~cond ~left ~right ff ex =
  if cond then begin
    fprintf ff left ;
    print ~left ~right ff ex ;
    fprintf ff right ;
  end else
    print ~left ~right ff ex

and kprint_bracket ~left ~right ff br =
  fprintf ff br.left ;
  print ~left ~right ff br.inner ;
  fprintf ff br.right
