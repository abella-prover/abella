(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

let stlc_sig = {stlc|
sig stlc.
  kind    tm, ty    type.
  type    app       tm -> tm -> tm.
  type    abs       ty -> (tm -> tm) -> tm.
  type    arrow     ty -> ty -> ty.
  type    of        tm -> ty -> o.
end.|stlc}

let stlc_mod = {stlc|
module stlc.
  of (abs T R) (arrow T U) :- pi x\ (of x T => of (R x) U).
  of (app M N) T :- of M (arrow U T), of N U.
end.|stlc}

let stlc_thm = {stlc|
%% Type uniqueness for the simply-typed lambda-calculus

Specification "stlc".

%% There are some results about nominal variables, freshness, and lists
%% that we can prove in general.

%% Start generic section

Define name : tm -> prop by
  nabla x, name x.

% Theorem member_prune : forall G E, nabla (n:tm),
%  member (E n) G -> (exists E', E = x\E').
% induction on 1. intros. case H1.
%  search.
%  apply IH to H2. search.

Theorem member_nominal_absurd : forall L T, nabla x,
  member (of x T) L -> false.
induction on 1. intros. case H1. apply IH to H2.

%% End generic section

Close tm, ty.

Define ctx : olist -> prop by
  ctx nil ;
  nabla x, ctx (of x T :: L) := ctx L.

Theorem ctx_uniq : forall L E T1 T2,
 ctx L -> member (of E T1) L -> member (of E T2) L -> T1 = T2.
induction on 2. intros. case H2.
 case H3.
   search.
   case H1. apply member_nominal_absurd to H4.
 case H3.
   case H1. apply member_nominal_absurd to H4.
   case H1. apply IH to H6 H4 H5. search.

Theorem ctx_mem :
   forall L E,
   ctx L -> member E L ->
   exists N X, E = of X N /\ name X.
induction on 2. intros. case H2.
  case H1. search.
  case H1.
    apply IH to H4 H3. search.

Theorem type_uniq_ext : forall L E T1 T2,
 ctx L -> {L |- of E T1} -> {L |- of E T2} -> T1 = T2.
induction on 2. intros. case H2.
 case H3.
   apply IH to _ H4 H5. search.
   apply ctx_mem to H1 H6. case H7. case H5.
 case H3.
   apply IH to H1 H4 H6. search.
   apply ctx_mem to H1 H7. case H8. case H6.
 apply ctx_mem to H1 H5. case H4. case H6.
   case H3. apply ctx_mem to H1 H8. case H7.
   apply ctx_uniq to H1 H5 H8. search.

Theorem type_uniq : forall E T1 T2,
 {of E T1} -> {of E T2} -> T1 = T2.
 intros. apply type_uniq_ext to _ H1 H2. search.
|stlc}

let cache : (string, string) Hashtbl.t = Hashtbl.create 19

let init () =
  List.iter begin fun (name, contents) ->
    Hashtbl.add cache name contents
  end [
    "./stlc.sig", stlc_sig ;
    "./stlc.mod", stlc_mod ;
    "stlc.thm", stlc_thm ;
  ]

let () = init ()

let reset () =
  Hashtbl.clear cache ;
  init ()

let get nm =
  if Hashtbl.mem cache nm then Hashtbl.find cache nm else
  let ch = open_in_bin nm in
  let buf = Buffer.create 19 in
  let () = try begin
    while true do Buffer.add_string buf (input_line ch) done
  end with End_of_file -> () in
  let file_contents = Buffer.contents buf in
  Hashtbl.replace cache nm file_contents ;
  file_contents

let lexbuf filename =
  let lexbuf = Lexing.from_string (get filename) in
  lexbuf.Lexing.lex_curr_p <- {
    lexbuf.Lexing.lex_curr_p with
    Lexing.pos_fname = filename } ;
  lexbuf
