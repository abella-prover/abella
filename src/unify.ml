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

(** Higher Order Pattern Unification *)

type error =
  | OccursCheck
  | TypesMismatch
  | ConstClash of (Term.term * Term.term)

exception Error of error
exception NotLLambda of Term.term

let not_ll x = raise (NotLLambda x)
let raise e = raise (Error e)

module type Param =
sig
  val instantiatable : Term.tag
  val constant_like  : Term.tag
end

module Make (P:Param) =
struct

open P
open Term
open Extensions

let used = ref []

let named_fresh name ts =
  let (v, new_used) = fresh_wrt instantiatable ts name !used in
    used := new_used ;
    v

let constant tag =
  tag = Constant || tag = constant_like || tag = Nominal
let variable tag =
  tag = instantiatable
let fresh = Term.fresh ~tag:instantiatable

(* Transforming a term to represent substitutions under abstractions *)
let rec lift t n = match Term.observe t with
  | Var _ -> t
  | DB i -> db (i+n)
  | _ -> susp t 0 n []

(* Transforming a list of arguments to represent eta fluffing *)
let rec lift_args l n = match l,n with
  | [],0 -> []
  | [],n -> (db n)::lift_args [] (n-1)
  | (a::rargs),n -> (lift a n)::lift_args rargs n

(* Check wether a Var appears in a list of terms *)
let rec unique_var v = function
  | [] -> true
  | t::rargs  ->
      begin match observe t with
        | Var v' when v=v' -> false
        | _ -> unique_var v rargs
      end

(* Check if a bound variable appears in a list of term *)
let rec unique_bv n l = match l with
  | [] -> true
  | t::rargs ->
      begin match observe t with
        | DB j when n = j -> false
        | _ -> unique_bv n rargs
      end

(** [check_flex_args l fts] checks that a list of terms meets the LLambda
  * requirements for the arguments of a flex term whose timestamp is [fts].
  * @raise NotLLambda if the list doesn't satisfy the requirements. *)
let rec check_flex_args l fts =
  match l with
    | [] -> ()
    | t::q ->
        begin match Term.observe t with
          | Var v when constant v.tag && v.ts>fts && unique_var v q ->
              check_flex_args q fts
          | DB i when unique_bv i q -> check_flex_args q fts
          | _ -> not_ll t
        end

(** [bvindex bv l n] return a nonzero index iff the db index [bv]
  * appears in [l]; the index is the position from the right, representing
  * the DeBruijn index of the abstraction capturing the argument.
  * Arguments in the list are expected to be head-normalized. *)
let rec bvindex i l n = match l with
  | [] -> 0
  | t::q ->
     begin match Term.observe t with
       | Term.DB j when i=j -> n
       | _ -> bvindex i q (n-1)
     end

(** [cindex c l n] return a nonzero index iff the constant [c]
  * appears in [l]; the index is the position from the right, representing
  * the DeBruijn index of the abstraction capturing the argument.
  * Arguments in the list are expected to be head-normalized. *)
let rec cindex c l n = match l with
  | [] -> 0
  | t::q ->
      begin match Term.observe t with
        | Var c' when c = c' -> n
        | _ -> cindex c q (n-1)
      end

(** Given a flexible term [v1 a11 ... a1n] and another term of the form 
  * [... (v2 a21 ... a2m) ...] where [v1] and [v2] are distinct variables,
  * [ts1] and [ts2] being the timestamps associated with [v1] and [v2],
  * and [lev] being the number of abstractions under which [v2] appears
  * embedded in the second term,
  * [raise_and_invert ts1 ts2 [a11 .. a1n] [a21 .. a2m] lev]
  * return a triple consisting of:
  *
  * {ul
  * {li a truth value indicating whether a pruning or raising
  * substitution is needed for [v2],}
  * {li a list of terms [b1 ... bk] such that the term 
  * [Lam ... Lam (... (v2' b1 ... bk) ...] 
  * represents a unifying substitution for [v1] -- these terms 
  * consist of constants from [a11 ... a1n] over which [v2] is
  * possibly raised and inversions of a pruned [a21 ... a2m], and}
  * {li the arguments [c1 ... ck] of a possible "raising" and pruning
  * substitution for [v2] matching the arguments [b1 ... bk] for
  * [v2'] in the second component.}}
  *
  * The composition of the arguments lists can be understood
  * qualitatively as follows:
  *
  * If [ts1 < ts2] then {ul{li the initial part of
  * [b1 ... bk] is the indices of constants from [a11 ... a1n] that do
  * not appear in [a21 ... a2m] and that have a timestamp less than or 
  * equal to [ts2] (this corresponds to raising [v2]) and} {li the rest of 
  * [b1 ... bk] are the indices (relative to the list a11 ... a1n) of 
  * the constants in [a21 ... a2m] that appear in [a11 ... a1n] (these are 
  * the arguments that must not be pruned).}} Correspondingly, the first
  * part of the list [c1 ... ck] are the constants from [a11 ... a1n] over
  * which [v2] is "raised" and the second part are the indices relative
  * to [a21 ... a2m] of the constants that are not pruned.
  *
  * If [ts1 >= ts2]
  * then each of [b1 ... bk] is either {ul{li a constant in [a21 ... a2m] that
  * does not appear in [a11 ... a1n] and which has a timestamp less than
  * [ts1] (this corresponds to first raising [v1] and then reducing the
  * substitution generated for [v1])} {li or it is the index, relative to 
  * [a11 ... a1n], of the terms in [a21 ... a2m] that are in 
  * [a11 ... a1n].}}
  * The list [c1 ... ck] in this case are simply the indices
  * relative to [a21 ... a2m] of the terms in [a21 ... a2m] that are
  * preserved (i.e. not pruned) in [b1 ... bk].
  * 
  * This definition assumes that the [aij] are in
  * head-normal form and that [a1] satisfies the LLambda 
  * requirements. If [a2] does not satisfy these requirements, an
  * exception will be raised. *)
let raise_and_invert ts1 ts2 a1 a2 lev =
  let l1 = List.length a1 in

  (* [raise_var args n] generates the collection of
   * constants in [args] that have a time stamp less than [ts2],
   * assuming [n] is the index for the abstraction corresponding
   * to the first term in [args]. In other words, constants which cannot
   * appear in [v2]'s body. This
   * serves to raise [v2] in the case where [ts1 < ts2]. The boolean
   * component of the returned triple tells if there is
   * any raising to be done. The terms in [args] are assumed to be
   * constants or de Bruijn indices, as head normalized
   * arguments satisfying the LLambda restriction. *)
  let rec raise_var l n = match l with
    | [] -> false,[],[]
    | t::tl ->
        begin match Term.observe t with
          | Term.DB _ -> raise_var tl (n-1)
          | Term.Var {ts=cts;tag=tag} when constant tag ->
              let raised,inds,consts = raise_var tl (n-1) in
                if cts<=ts2
                then (true,(Term.db (n+lev))::inds,t::consts)
                else (raised,inds,consts)
          | _ -> assert false
        end
  in

  (** [prune args n] "prunes" those items in [args] that are not
    * bound by an embedded abstraction and that do not appear in
    * [a1]. At the same time inverts the items that are not pruned
    * and that are not bound by an embedded abstraction; [n] is assumed to be
    * the length of [args] here and hence yields the index of the
    * leftmost argument position. This pruning computation is
    * relevant to the case when [ts1 < ts2]. The terms in [args]
    * are assumed to be constants or de Bruijn indices. *)
  let rec prune l n = match l,n with
    | [],0 -> false,[],[]
    | t::q,n ->
        begin match Term.observe t with
          | Term.DB i -> 
              let pruned,inds1,inds2 = prune q (n-1) in
                if i > lev then
                  let j = bvindex (i-lev) a1 l1 in
                    if j = 0 then
                      (true,inds1,inds2) 
                    else
                      (pruned,
                       (Term.db (j+lev))::inds1,
                       (Term.db n)::inds2)
                else
                  (pruned,t::inds1,(Term.db n)::inds2)
          | Term.Var v when constant v.tag ->
              let (pruned,inds1,inds2) = prune q (n-1) in
              let j = cindex v a1 l1 in
                if j = 0 then
                  (true,inds1,inds2)
                else
                  (pruned,
                   (Term.db (j+lev))::inds1,
                   (Term.db n)::inds2)
          | _ -> assert false
        end
    | _ -> assert false
  in

  (** Relevant to the case when [ts1 > ts2]. In this case,
    * [prune_and_raise args n] prunes those constants and de
    * Bruijn indices not bound by an embedded abstraction that do
    * not appear in [a1] and, in the case of constants, that do not
    * have a timestamp less than [ts1]. Constants that do have a timestamp
    * greater than or equal to [ts1] are preserved via a raising of
    * [v1]. As in prune, [n] is assumed to be the length of the list
    * args. The terms in [args] are assumed to be constants or de
    * Bruijn indices. *)
  let rec prune_and_raise l n = match l,n with
    | [],0 -> false,[],[]
    | a::q,n ->
        begin match Term.observe a with
          | Term.DB i -> 
              let (pruned,inds1,inds2) = prune_and_raise q (n-1) in
                if i > lev then
                  let j = bvindex (i-lev) a1 l1 in
                    if j = 0 then
                      (true,inds1,inds2)
                    else
                      (pruned,
                       (Term.db (j+lev))::inds1,
                       (Term.db n)::inds2)
                else (pruned,a::inds1,(Term.db n)::inds2)
          | Term.Var v when constant v.tag -> 
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
                if v.ts <= ts1 then
                  (pruned,a::inds1,(Term.db n)::inds2)
                else
                  let i = cindex v a1 l1 in
                    if i=0 then
                      (true,inds1,inds2)
                    else
                      (pruned,
                       (Term.db (i+lev))::inds1,
                       (Term.db n)::inds2)
          | _ -> assert false
        end
    | _ -> assert false
  in

    if ts1<ts2 then
      let raised,args11,args12 = raise_var a1 l1 in
      let pruned,args21,args22 = prune a2 (List.length a2) in
        (raised||pruned,args11@args21,args12@args22)
    else
      prune_and_raise a2 (List.length a2)

(* Generating the arguments of a pruning substitution for the case
 * when trying to unify two flexible terms of the form (v t1 ... tn)
 * and lam ... lam (v s1 ... sm) where there are j abstractions at the 
 * head of the second term. The first two arguments to prune_same_var
 * are the two lists of arguments, the third argument is j (i.e. the
 * number of abstractions at the head) and the last argument is n+j. It
 * is assumed that type consistency has been checked beforehand,
 * i.e. n+j is indeed equal to m and also that the two argument lists
 * are known to be of the form required for LLambda unification. The
 * computation essentially does the eta fluffing of the first term on
 * the fly (i.e. each ti has to be lifted over j abstractions and and
 * j new arguments bound by these abstractions are added to the first
 * term). *)
let rec prune_same_var l1 l2 j bl = match l1,l2 with
  | [],[] -> []
  | [],t::q ->
      begin match Term.observe t with
        | Term.DB i when i=j ->
            (Term.db bl)::(prune_same_var [] q (j-1) (bl-1))
        | _ -> prune_same_var [] q (j-1) (bl-1)
      end
  | t1::a1,t2::a2 ->
      begin match Term.observe t1,Term.observe t2 with
        | Term.Var {tag=tag1},Term.Var {tag=tag2}
          when tag1=tag2 && constant tag1 && Term.eq t1 t2 ->
            (Term.db bl)::(prune_same_var a1 a2 j (bl-1))
        | Term.DB i1,Term.DB i2     when i1+j = i2 ->
            (Term.db bl)::(prune_same_var a1 a2 j (bl-1))
        | _ -> prune_same_var a1 a2 j (bl-1)
      end
  | _ -> assert false

(** [makesubst h1 t2 a1 n] unifies [App (h1,a1) = t2].
  * Given a term of the form [App (h1,a1)] where [h1] is a variable and
  * another term [t2], generate an LLambda substitution for [h1] if this is 
  * possible, making whatever pruning and raising substitution that are
  * necessary to variables appearing within [t2].
  *
  * [t2] is assumed to be in head normal form, [h1] and [a1] are assumed to be
  * dereferenced, and [n] is supposed to be the length of [a1].
  * 
  * Exceptions can be
  * raised from this code if a non LLambda situation is discovered or
  * there is failure in unification or a type mismatch (possible if an
  * a priori type checking has not been done) is encountered.
  *
  * The unification computation is split into two parts, one that
  * examines the top level structure of [t2] and the other that descends
  * into its nested subparts. This organization is useful primarily
  * because [h1], the variable head of the first term can appear at the
  * toplevel in t2 without sacrificing unifiability but not in a nested
  * part. *)
let makesubst h1 t2 a1 n =
  (* Check that h1 is a variable, get its timestamp *)
  let hv1 = match Term.observe h1 with
    | Term.Var v -> assert (v.tag=instantiatable) ; v
    | _ -> assert false
  in
  let ts1 = hv1.ts in
  let a1 = List.map hnorm a1 in

  (** Generating a substitution term and performing raising and
    * pruning substitutions corresponding to a non top-level
    * (sub)term. In this case the variable being bound cannot appear
    * embedded inside the term. This code assumes that its term
    * argument is head normalized. Exceptions can be
    * raised if unification fails or if LLambda conditions are found
    * to be violated. *)
  let rec nested_subst c lev =
    match Term.observe c with
      | Term.Var v when constant v.tag ->
          (* Can [h1] depend on [c] ?
           * If so, the substitution is [c] itself -- why couldn't we pick an
           * argument in that case too ? TODO
           * If not, [c] must belong to the argument list. *)
          if v.ts <= ts1 then c else
            let j = cindex v a1 n in
              if j = 0 then raise OccursCheck ;
              Term.db (j+lev)
      | Term.DB i ->
          if i<=lev then c else
            let j = bvindex (i-lev) a1 n in
              if j = 0 then raise OccursCheck ;
              Term.db (j+lev)
      | Term.Var {ts=ts2;tag=tag} when variable tag ->
          if Term.eq c h1 then raise OccursCheck ;
          let (changed,a1',a2') = raise_and_invert ts1 ts2 a1 [] lev in
            if changed || ts1<ts2 then
              let h'=
                if ts1<ts2 then fresh ts1
                else fresh ts2
              in
                (* TODO read carefuly *)
                Term.bind c (Term.app h' a2') ;
                Term.app h' a1'
            else
              Term.app c a1'
      | Term.Lam (n,t) ->
          Term.lambda n (nested_subst t (lev+n))
      | Term.App (h2,a2) ->
          begin match Term.observe h2 with
            | Term.Var {tag=tag} when constant tag ->
                (* TODO I'm defeated here ;) wtf is the invariant ? *)
                let a2 = List.map hnorm a2 in
                Term.app
                  (nested_subst h2 lev)
                  (List.map (fun x -> nested_subst x lev) a2)
            | Term.DB _ -> 
                (* TODO I'm defeated here ;) wtf is the invariant ? *)
                let a2 = List.map hnorm a2 in
                Term.app
                  (nested_subst h2 lev)
                  (List.map (fun x -> nested_subst x lev) a2)
            | Term.Var {ts=ts2;tag=tag} when tag=instantiatable ->
                if Term.eq h2 h1 then raise OccursCheck ;
                let a2 = List.map hnorm a2 in
                check_flex_args a2 ts2 ;
                let changed,a1',a2' =
                  raise_and_invert ts1 ts2 a1 a2 lev
                in
                  if changed then
                    let h' =
                      (* TODO - is this special case for a1 = [] sound? *)
                      if a1 = []
                      then named_fresh hv1.name (min ts1 ts2)
                      else fresh (min ts1 ts2)
                    in
                      Term.bind h2
                        (Term.lambda (List.length a2)
                           (Term.app h' a2')) ;
                      Term.app h' a1'
                  else
                    if ts1<ts2 then
                      let h' = fresh ts1 in
                        Term.bind h2 h' ;
                        Term.app h' a1'
                    else 
                      Term.app h2 a1'
            | Var _ -> failwith "logic variable on the left (1)"
            | _ -> assert false
          end
      | Var _ -> failwith "logic variable on the left (2)"
      | _ -> assert false
  in

  (** Processing toplevel structure in generating a substitution.
    * First descend under abstractions. Then if the term is a
    * variable, generate the simple substitution. Alternatively, if
    * it is an application with the variable being bound as its head,
    * then generate the pruning substitution. In all other cases,
    * pass the task on to nested_subst. An optimization is possible
    * in the case that the term being examined has no outer
    * abstractions (i.e. lev = 0) and its head is a variable with a
    * time stamp greater than that of the variable being bound. In
    * this case it may be better to invoke raise_and_invert
    * directly with the order of the "terms" reversed.
    *
    * The incoming term is assumed to be head normalized. *)

  let rec toplevel_subst t2 lev =
    match Term.observe t2 with
      | Term.Lam (n,t2) -> toplevel_subst t2 (lev+n)
      | Term.Var {tag=t} when variable t ->
          if h1=t2 then
            if n=0 && lev=0 then h1 else raise TypesMismatch
          else
            Term.lambda (lev+n) t2
      | Term.App (h2,a2) ->
          begin match Term.observe h2 with
            | Term.Var {ts=ts2} when Term.eq h1 h2 ->
                (* [h1] being instantiatable, no need to check it for [h2] *)
                let a2 = List.map hnorm a2 in
                check_flex_args a2 ts2 ;
                let bindlen = n+lev in
                  if bindlen = List.length a2 then
                    let h1' = fresh ts1 in
                    let args = prune_same_var a1 a2 lev bindlen in
                      Term.lambda bindlen (Term.app h1' args)
                  else
                    raise TypesMismatch
            | Term.App _ | Term.Lam _
            | Term.Var _ | Term.DB _ ->
                Term.lambda (n+lev) (nested_subst t2 lev)
            | Term.Susp _ | Term.Ptr _ -> assert false
          end
      | Term.Ptr _ -> assert false
      | _ -> Term.lambda (n+lev) (nested_subst t2 lev)
  in

    check_flex_args a1 ts1 ;
    toplevel_subst t2 0

(** Unifying the arguments of two rigid terms with the same head, these
  * arguments being given as lists. Exceptions are raised if
  * unification fails or if there are unequal numbers of arguments; the
  * latter will not arise if type checking has been done. *)
let rec unify_list l1 l2 =
  try
    List.iter2 (fun a1 a2 -> unify (hnorm a1) (hnorm a2)) l1 l2
  with
    | Invalid_argument _ -> raise TypesMismatch

(* [unify_const_term cst t2] unify [cst=t2], assuming that [cst] is a constant.
 * Fail if [t2] is a variable or an application.
 * If it is a lambda, binders need to be equalized and so this becomes
 * an application-term unification problem. *)
and unify_const_term cst t2 = if Term.eq cst t2 then () else
  match Term.observe cst, Term.observe t2 with
    | _, Term.Lam (n,t2) ->
        let a1 = lift_args [] n in
          unify_app_term cst a1 (Term.app cst a1) t2
    | _, Term.Var {tag=t} when not (variable t || constant t) ->
        failwith "logic variable on the left (3)"
    | _ -> raise (ConstClash (cst,t2))

(* Unifying the bound variable [t1] with [t2].
 * Fail if [t2] is a variable, an application or a constant.
 * If it is a lambda, binders need to be
 * equalized and this becomes an application-term unification problem. *)
and unify_bv_term n1 t1 t2 = match Term.observe t2 with
  | Term.DB n2 ->
      if n1<>n2 then raise (ConstClash (t1,t2))
  | Term.Lam (n,t2)  ->
      let t1' = lift t1 n in
      let a1 = lift_args [] n in
        unify_app_term t1' a1 (Term.app t1' a1) t2
  | Var {tag=t} when not (variable t || constant t) ->
      failwith "logic variable on the left (4)"
  | _ -> assert false

(* [unify_app_term h1 a1 t1 t2] unify [App h1 a1 = t2].
 * [t1] should be the term decomposed as [App h1 a1].
 * [t2] should be dereferenced and head-normalized, different from a var. *)
and unify_app_term h1 a1 t1 t2 = match Term.observe h1,Term.observe t2 with
  | Term.Var {tag=tag}, _ when variable tag ->
      let n = List.length a1 in
        Term.bind h1 (makesubst h1 t2 a1 n)
  | Term.Var v1, Term.App (h2,a2) when constant v1.tag ->
      begin match Term.observe h2 with
        | Var v2 when constant v2.tag ->
            if Term.eq h1 h2 then
              unify_list a1 a2
            else
              raise (ConstClash (h1,h2))
        | DB _ ->
            raise (ConstClash (h1,h2))
        | Var {tag=tag} when variable tag ->
            let m = List.length a2 in
              Term.bind h2 (makesubst h2 t1 a2 m)
        | Var {tag=t} when not (variable t || constant t) ->
            failwith "logic variable on the left (5)"
        | _ -> assert false
      end
  | _, Term.Lam (n,t2) ->
      let h1' = lift h1 n in
      let a1' = lift_args a1 n in
      let t1' = Term.app h1' a1' in
        unify_app_term h1' a1' t1' t2
  | Term.Ptr _, _ | _, Term.Ptr _
  | Term.Susp _, _ | _, Term.Susp _ -> assert false
  | Term.Var {tag=t}, _ when not (variable t || constant t) ->
      failwith "logic variable on the left (6)"
  | _ -> raise (ConstClash (h1,t2))

(** Here we assume t1 is a variable we want to bind to t2. We must check that
  * there is no-cyclic substitution and that nothing with a timestamp higher
  * than t1 is allowed. *)
and rigid_path_check t1 t2 =
  match Term.observe t1, Term.observe t2 with
    | Term.Var v1, Term.Var v2 when v1 = v2 -> false
    | Term.Var {ts=ts1}, Term.Var {ts=ts2} when ts2 > ts1 -> false
    | _, Term.Var _ -> true
    | _, Term.DB i -> true
    | _, Term.Lam(n2,t2) -> rigid_path_check t1 t2
    | Term.Var v1, Term.App(h2,a2) -> List.for_all (rigid_path_check t1) a2
    | _ -> false

(** The main unification procedure.
  * Either succeeds and realizes the unification substitutions as side effects
  * or raises an exception to indicate nonunifiability or to signal
  * a case outside of the LLambda subset. When an exception is raised,
  * it is necessary to catch this and at least undo bindings for
  * variables made in the attempt to unify. This has not been included
  * in the code at present.
  * 
  * This procedure assumes that the two terms it gets are in
  * head normal form and that there are no iterated
  * lambdas or applications at the top level. Any necessary adjustment
  * of binders through the eta rule is done on the fly. *)
and unify t1 t2 = match Term.observe t1,Term.observe t2 with
  | Term.Var v1, Term.Var v2 when v1 = v2 -> ()
  | Term.Var {tag=t},_ when variable t ->
      if rigid_path_check t1 t2 then
        Term.bind t1 t2
      else
        Term.bind t1 (makesubst t1 t2 [] 0)
  | _,Term.Var {tag=t} when variable t ->
      if rigid_path_check t2 t1 then
        Term.bind t2 t1
      else
        Term.bind t2 (makesubst t2 t1 [] 0)
  | Term.App (h1,a1),_                 -> unify_app_term h1 a1 t1 t2
  | _,Term.App (h2,a2)                 -> unify_app_term h2 a2 t2 t1
  | Term.Var {tag=t},_ when constant t -> unify_const_term t1 t2
  | _,Term.Var {tag=t} when constant t -> unify_const_term t2 t1
  | Term.DB n,_                        -> unify_bv_term n t1 t2
  | _,Term.DB n                        -> unify_bv_term n t2 t1
  | Term.Lam (n1,t1),Term.Lam(n2,t2)   ->
      if n1>n2 then
        unify (Term.lambda (n1-n2) t1) t2
      else
        unify t1 (Term.lambda (n2-n1) t2)
  | _ -> failwith "logic variable on the left (7)"

let pattern_unify used_names t1 t2 =
  used := used_names ;
  unify (hnorm t1) (hnorm t2)

end

module Right =
  Make (struct
          let instantiatable = Term.Logic
          let constant_like = Term.Eigen
        end)
    
module Left =
  Make (struct
          let instantiatable = Term.Eigen
          let constant_like = Term.Logic
        end)

let right_unify ?used:(used=[]) t1 t2 =
  Right.pattern_unify used t1 t2

let left_unify ?used:(used=[]) t1 t2 =
  let t1 = Term.set_nominal_timestamps 1000 t1 in
  let t2 = Term.set_nominal_timestamps 1000 t2 in
    Left.pattern_unify used t1 t2
      
let try_with_state f =
  let state = Term.get_bind_state () in
    try
      f ()
    with
      | _ -> Term.set_bind_state state ; false

let try_right_unify ?used:(used=[]) t1 t2 =
  try_with_state
    (fun () ->
       right_unify ~used:used t1 t2 ;
       true)
 
let try_left_unify ?used:(used=[]) t1 t2 =
  try_with_state
    (fun () ->
       left_unify ~used:used t1 t2 ;
       true)

