(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2013  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open PPrintEngine
open PPrintCombinators

type docexp =
  | Atom    of document
  | Wrap    of wrapping * document * docexp * document
  | Appl    of int * docappl

and docappl =
  | Prefix  of document * docexp
  | Postfix of docexp * document
  | Infix   of document * associativity * docexp list

and associativity = Left | Right | Non

and wrapping = Opaque | Transp

let maybe_enclose ~cond l r d =
  if cond then enclose l r d else d

let is_prefix = function
  | Appl (_, Prefix _) -> true
  | _ -> false

let is_postfix = function
  | Appl (_, Postfix _) -> true
  | _ -> false

(** [orec >? de] checks if [prec] represents a higher precedence than
    the topmost visible operator in [de]. Atomic and opaque-wrapped
    expressions have infinite precedence. *)
let rec ( >? ) prec de = match de with
  | Appl (subprec, _) when prec > subprec -> true
  | Wrap (Transp, _, de, _) -> prec >? de
  | _ -> false

(** [infix_incompat_p tasc prec asc de] is used when [de] is an
    operand in an infix expression where the parent operator has
    associativity [asc] and precedence [prec]. It succeeds when [de]
    needs to be bracketed.

    The [tasc] parameter is a "test" associativity: if [de] is also an
    infix operator with precedence [prec] and associativity [asc],
    then [de] does not need to be bracketed iff [tasc = asc]. For the
    first operand of an infix operator, [tasc = Left], and for the
    last operand [tasc = Right].

    Note that associativity is only relevant for the first and the
    last operands in an infix application. The middle operands are
    only tested for precedence.
*)
let rec infix_incompat_p tasc prec asc = function
  | Appl (subprec, (Prefix _ | Postfix _))
    when prec >= subprec -> true
  | Appl (subprec, Infix (_, subasc, _))
    when prec = subprec && not (asc = tasc && subasc = tasc) -> true
  | Wrap (Transp, _, de, _) ->
      infix_incompat_p tasc prec asc de
  | _ -> false

let rec bracket ~left ~right = function
  | Atom d -> d
  | Wrap (_, ldl, de, rdl) ->
      enclose ldl rdl (bracket ~left ~right de)
  | Appl (prec, appl) -> begin
      match appl with
      | Prefix (op, de) ->
          let d = bracket ~left ~right de in
          prefix 2 1 op
            (maybe_enclose left right d
               ~cond:(prec >? de && not (is_prefix de)))
      | Postfix (de, op) ->
          let d = bracket ~left ~right de in
          prefix 1 1
            (maybe_enclose left right d
               ~cond:(prec >? de && not (is_postfix de))) op
      | Infix (op, asc, de0 :: des) ->
          let (des, deN) = match List.rev des with
            | deN :: des -> (List.rev des, deN)
            | _ -> failwith "bracket: Infix needs at least two operands"
          in
          let d0 =
            maybe_enclose left right (bracket ~left ~right de0)
              ~cond:(prec >? de0
                     || infix_incompat_p Left prec asc de0) in
          let dN =
            maybe_enclose left right (bracket ~left ~right deN)
              ~cond:(prec >? deN
                     || infix_incompat_p Right prec asc deN) in
          let ds = List.map begin fun de ->
              maybe_enclose left right (bracket ~left ~right de)
                ~cond:(prec >? de)
            end des in
          List.fold_right
            (fun d1 d2 -> infix 2 1 op d1 d2)
            (d0 :: ds) dN
      | Infix _ -> failwith "bracket: Infix needs at least one operand"
    end

(* The above function is very straightforward, but it has a major
   deficiency: it does not treat the precedence of prefix/postfix
   operators correctly.

   Consider this situation:

   | operator | kind   | associativity | precedence |
   |----------+--------+---------------+------------|
   | ~        | prefix | ---           |          3 |
   | +        | infix  | left          |          2 |
   | !        | prefix | ---           |          1 |

   with this example: (~!a) + b.

   The naive algorithm above sees that ~ has higher precedence than +,
   so it doesn't bother bracketing ~!a, so the result is: ~!a + b.
   However, because ! has lowermost precedence, this would have to be
   interpreted as ~!(a + b).

   To fix this, we must *modify* the precedence of ~ in ~!a to the
   precedence of ! to expose the fact ! can conflict with ancestral
   infix operators. This is achieved by propagating the currently
   dominant (= lowest precedence) pre/postfix operator upwards in the
   subexpression hierarchy.
*)

type dom_op = PRE of int | POST of int | NOP

let rec mod_prec de = match de with
  | Atom _ -> (de, NOP)
  | Appl (prec, Infix (op, asc, des)) ->
      let des = List.map (fun de -> fst (mod_prec de)) des in
      (Appl (prec, Infix (op, asc, des)), NOP)
  | Appl (prec, Prefix (op, de)) ->
      let (de, dom) = mod_prec de in
      let prec = match dom with
        | PRE dprec -> min prec dprec
        | _ -> prec
      in
      (Appl (prec, Prefix (op, de)), PRE prec)
  | Appl (prec, Postfix (de, op)) ->
      let (de, dom) = mod_prec de in
      let prec = match dom with
        | POST dprec -> min prec dprec
        | _ -> prec
      in
      (Appl (prec, Postfix (de, op)), POST prec)
  | Wrap (w, l, de, r) ->
      let (de, dom) = mod_prec de in
      let dom = match w with
        | Transp -> dom
        | Opaque -> NOP
      in
      (Wrap (w, l, de, r), dom)

let bracket ?(left=lparen) ?(right=rparen) de =
  let (de, _) = mod_prec de in
  bracket ~left ~right de

(* some tests *)
(*
let dump de =
  ToChannel.pretty 1. 80 stdout (bracket de) ; print_endline ""
let a = Atom (string "a")
let b = Atom (string "b")
let c = Atom (string "c")
let bang de = Appl (1, Prefix (string "!", de))
let tilde de = Appl (4, Prefix (string "~", de))
let plus des = Appl (2, Infix (string "+", Left, des))
let times des = Appl (3, Infix (string "*", Left, des))
let de0 = plus [times [a ; b] ; c]
let de1 = times [plus [a ; b] ; c]
let de2 = plus [de0 ; de1]
let de3 = times [de0 ; de1]
let de4 = plus [tilde (bang a) ; b]
let () = List.iter dump [de0 ; de1 ; de2 ; de3 ; de4]
*)
