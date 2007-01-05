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

(* (Lazy Head) Normalization *)

(** Make an environment appropriate to [n] lambda abstractions applied to
    the arguments in [args]. Return the environment together with any
    remaining lambda abstractions and arguments. (There can not be both
    abstractions and arguments left over). *)
let make_env n args =
  let rec aux n args e =
    if n = 0 || args = []
    then (e, n, args)
    else aux (n-1) (List.tl args) (Term.Binding(List.hd args, 0)::e)
  in aux n args []
        
(** Head normalization function.*)
let rec hnorm term =
  match Term.observe term with
    | Term.Var _
    | Term.DB _
    | Term.NB _ -> term
    | Term.Lam(n,t) -> Term.lambda n (hnorm t)
    | Term.App(t,args) ->
        let t = hnorm t in
          begin match Term.observe t with
            | Term.Lam(n,t) ->
                let e, n', args' = make_env n args in
                let ol = List.length e in
                  if n' > 0
                  then hnorm (Term.susp (Term.lambda n' t) ol 0 e)
                  else hnorm (Term.app (Term.susp t ol 0 e) args')
            | _ -> Term.app t args
          end
    | Term.Susp(t,ol,nl,e) ->
        let t = hnorm t in
          begin match Term.observe t with
            | Term.NB _ | Term.Var _ -> t
            | Term.DB i ->
                if i > ol then
                  (* The index points to something outside the suspension *)
                  Term.db (i-ol+nl)
                else
                  (* The index has to be substituted for [e]'s [i]th element *)
                  begin match List.nth e (i-1) with
                    | Term.Dum l -> Term.db (nl - l)
                    | Term.Binding (t,l) -> hnorm (Term.susp t 0 (nl-l) [])
                  end
            | Term.Lam(n,t) ->
                Term.lambda n (hnorm (Term.susp t (ol+n) (nl+n)
                                       (Term.add_dummies e n nl)))
            | Term.App(t,args) ->
                let wrap x = Term.susp x ol nl e in
                  hnorm (Term.app (wrap t) (List.map wrap args))
            | Term.Susp _ -> hnorm (Term.susp (hnorm t) ol nl e)
            | Term.Ptr _ -> assert false
          end
    | Term.Ptr _ -> assert false

let rec deep_norm t =
  let t = hnorm t in
    match Term.observe t with
      | Term.NB _ | Term.Var _ | Term.DB _ -> t
      | Term.Lam (n,t) -> Term.lambda n (deep_norm t)
      | Term.App (a,b) ->
            begin match Term.observe a with
              | Term.Var _ | Term.DB _ ->
                    Term.app a (List.map deep_norm b)
              | _ -> deep_norm (Term.app (deep_norm a) (List.map deep_norm b))
            end
      | Term.Ptr _ | Term.Susp _ -> assert false
