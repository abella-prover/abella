(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2006 David Baelde, Alwen Tiu, Axelle Ziegler          *)
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

exception Invalid_definition
exception Level_inconsistency

open Format
open System
open Term

(* Internal design of the prover has two levels, Zero and One.
 * On level One, logic vars are instantiated and eigenvars are constants.
 * On level Zero, logic vars are forbidden and eigenvars can be instantiated. *)

type level = Zero | One

let assert_level_one = function
  | One -> ()
  | Zero -> raise Level_inconsistency

module Right =
  Unify.Make (struct
                let instantiatable = Logic
                let constant_like = Eigen
              end)
module Left =
  Unify.Make (struct
                let instantiatable = Eigen
                let constant_like = Constant
              end)

let unify lvl a b =
  try
    (if lvl = Zero then Left.pattern_unify else Right.pattern_unify) a b ;
    true
  with
    | Unify.Error _ -> false

(* Tabling provides a way to cut some parts of the search,
 * but we should take care not to mistake shortcuts and disproving. *)

let disprovable_stack = Stack.create ()

let clear_disprovable () =
  try
    while true do
      let s,_ = Stack.pop disprovable_stack in s := Table.Unset
    done
  with Stack.Empty -> ()

exception Found
let mark_not_disprovable_until d =
  try
    Stack.iter (fun (_,disprovable) ->
      if disprovable == d
      then raise Found
      else disprovable := false)
      disprovable_stack
  with Found -> ()
  
type 'a answer = Known of 'a | Unknown | OffTopic

(* Attemps to prove that the goal [(nabla x_1..x_local . g)(S)] by
 * destructively instantiating it,
 * calling [success] on every success, and finishing with [failure]
 * which can be seen as a more usual continuation, typically
 * restoring modifications and backtracking.
 * [timestamp] must be the oldest timestamp in the goal. *)
let rec prove ~success ~failure ~level ~timestamp ~local g =

  if System.check_interrupt () then begin
    clear_disprovable () ;
    raise System.Interrupt
  end ;

  let state = Term.save_state () in
  let failure () =
    if !debug then
      Format.printf "No (more) success for %a\n" Pprint.pp_term g ;
    Term.restore_state state ;
    failure ()
  in
  let success k =
    if !debug then
      Format.printf "Success for           %a\n" Pprint.pp_term g ;
    success k
  in

  let g = Norm.hnorm g in

  if !debug then
    printf "Proving %a...\n" Pprint.pp_term g ;

  let prove_atom d args =
    let kind,body,table = System.get_def ~check_arity:(List.length args) d in
    let status =
      match table with
        | None -> OffTopic
        | Some table ->
            try match Table.find table args with
              | Some {contents=c} -> Known c
              | None -> Unknown
            with
              | Index.Cannot_table -> OffTopic
    in
      match status with
        | OffTopic ->
            prove ~level ~timestamp ~local ~success ~failure
              (Term.app body args)
        | Known Table.Proved -> success failure
        | Known Table.Disproved -> failure ()
        | Known (Table.Working disprovable) ->
            if kind = System.CoInductive then
              success failure
            else begin
              mark_not_disprovable_until disprovable ;
              failure ()
            end
        | Unknown
        | Known Table.Unset ->
            (* This handles the cases where nothing is in the table,
             * or Unset has been left, in which case the [Table.add]
             * will overwrite it. *)
            let disprovable = ref true in
            let status = ref (Table.Working disprovable) in
            let table_update_success k =
              status := Table.Proved ;
              ignore (Stack.pop disprovable_stack) ;
              disprovable := false ;
              (* TODO check that optimization: since we know that
               * there is at most one success, we ignore
               * the continuation [k] and directly jump to the
               * [failure] continuation. It _seems_ OK regarding the
               * cleanup handlers, which are just jumps to
               * previous states.
               * It is actually quite useful in graph-alt.def. *)
              success failure
            in
            let table_update_failure () =
              begin match !status with
                | Table.Proved ->
                    (* This is just backtracking, don't worry. *)
                    ()
                | Table.Working _ ->
                    ignore (Stack.pop disprovable_stack) ;
                    if !disprovable then begin
                      status := Table.Disproved ;
                      disprovable := false ;
                    end else
                      status := Table.Unset
                | _ -> assert false
              end ;
              failure ()
            in
            let table = match table with Some t -> t | None -> assert false in
              if try
                Table.add ~allow_eigenvar:(level=One) table args status ;
                true
              with
                | Index.Cannot_table -> false
              then begin
                Stack.push (status,disprovable) disprovable_stack ;
                prove ~level ~timestamp ~local
                  ~success:table_update_success
                  ~failure:table_update_failure
                  (Term.app body args)
              end else
                prove ~level ~timestamp ~local ~success ~failure
                  (Term.app body args)
  in

  match Term.observe g with
  | Var {name=t} when t = "exit" -> exit 0
  | Var {name=t} when t = Logic.truth -> success failure
  | Var {name=t} when t = Logic.falsity -> failure ()
  | Var {name=d;tag=Constant} -> prove_atom d []
  | App (hd,goals) ->
      let goals = List.map Norm.hnorm goals in
      begin match Term.observe hd with

        (* Solving an equality *)
        | Var {name=e} when e = Logic.eq && List.length goals = 2 ->
            if unify level (List.hd goals) (List.hd (List.tl goals)) then
              success failure
            else
              failure ()

        (* Proving a conjunction *)
        | Var {name=a} when a = Logic.andc ->
            let rec conj failure = function
              | [] -> success failure
              | goal::goals ->
                  prove
                    ~local ~timestamp ~level
                    ~success:(fun k -> conj k goals)
                    ~failure
                    goal
            in
              conj failure goals

        (* Proving a disjunction *)
        | Var {name=o} when o = Logic.orc ->
            let rec alt = function
              | [] -> failure ()
              | g::goals ->
                  prove
                    ~level ~local ~timestamp
                    ~success
                    ~failure:(fun () -> alt goals)
                    g
            in
              alt goals

        (* Level 1: Implication *)
        | Var {name=i} when i = Logic.imp && List.length goals = 2 ->
            assert_level_one level ;
            let (a,b) = match goals with [a;b] -> a,b | _ -> assert false in
            (* Solve [a] using level 0,
             * remind of the solution substitutions as slices of the bind stack,
             * then prove [b] at level 1 for every solution for [a],
             * thanks to the commutability between patches for [a] and [b],
             * one modifying eigenvars,
             * the other modifying logical variables. *)
            let ev_substs = ref [] in
            let store_subst k =
              (* We store the state in which we should leave the system
               * when calling [k].
               * The we complete the current solution with the reverse
               * flip of variables to eigenvariables, and we get sigma which
               * we store. *)
              ev_substs := (get_subst state)::!ev_substs ;
              k ()
            in
            let rec prove_b failure = function
              | [] -> success failure
              | sigma::substs ->
                  (* We have to prove (b theta_0 sigma_i) *)
                  let unsig = ref (apply_subst sigma) in
                    prove ~level ~local ~timestamp b
                    ~success:(fun k ->
                                (* We found (b theta_0 sigma_i theta).
                                 * Temporarily remove sigma_i to
                                 * prove (b theta_0 theta) against other
                                 * sigmas in substs. *)
                                undo_subst !unsig ;
                                prove_b
                                  (fun () ->
                                     (* Put sigma_i to restore the environment
                                      * for the next successes of (b sigma_i) *)
                                     unsig := apply_subst sigma ;
                                     k ())
                                  substs)
                    ~failure:(fun () ->
                                undo_subst !unsig ;
                                failure ())
            in
              prove ~level:Zero ~local ~timestamp a
                ~success:store_subst
                ~failure:(fun () ->
                            prove_b failure !ev_substs)

        (* Level 1: Universal quantification *)
        | Var {name=forall} when forall = Logic.forall ->
            assert_level_one level ;
            let goal = match goals with
              | [g] -> g
              | _ -> assert false
            in begin match observe goal with
              | Lam (1,_) ->
                  let timestamp = timestamp + 1 in
                  let var = Term.fresh ~lts:local ~tag:Eigen timestamp in
                  let goal = app goal [var] in
                    prove ~timestamp ~local ~level ~success ~failure goal
              | _ -> assert false
            end

        (* Local quantification *)
        | Var {name=nabla} when nabla = Logic.nabla ->
            let goal = match goals with
              | [g] -> g
              | _ -> assert false
            in begin match observe goal with
              | Lam (1,_) ->
                  let local = local + 1 in
                    prove ~timestamp ~local ~level ~success ~failure
                      (app goal [Term.nabla local])
              | _ -> assert false
            end

        (* Existential quantification *)
        | Var {name=ex} when ex = Logic.exists ->
            let goal = match goals with
              | [g] -> g
              | _ -> assert false
            in begin match observe goal with
              | Lam (1,_) ->
                  let var =
                    let tag = if level = Zero then Eigen else Logic in
                      Term.fresh ~lts:local ~tag timestamp
                  in
                    prove ~timestamp ~local ~level ~success ~failure
                      (app goal [var])
              | _ -> assert false
            end

        (* Output *)
        | Var {name="print"} ->
            List.iter (fun t -> printf "%a\n%!" Pprint.pp_term t) goals ;
            success failure

        (* Check for definitions *)
        | Var {name=d;tag=Constant} -> prove_atom d goals

        (* Invalid goal *)
        | _ ->
            printf "Invalid goal %a!" Pprint.pp_term g ;
            failure ()
      end

  (* Failure *)
  | _ ->
      printf "Invalid goal %a!" Pprint.pp_term g ;
      failure ()

let prove ~success ~failure ~level ~timestamp ~local g =
  try
    prove ~success ~failure ~level ~timestamp ~local g
  with e -> clear_disprovable () ; raise e

let toplevel_prove g =
  let _ = Term.reset_namespace () in
  let s0 = Term.save_state () in
  let vars = List.map (fun t -> Pprint.term_to_string t, t)
               (List.rev (Term.logic_vars [g])) in
  let found = ref false in
  let reset,time =
    let t0 = ref (Unix.gettimeofday ()) in
      (fun () -> t0 := Unix.gettimeofday ()),
      (fun () ->
         if !System.time then
           printf "+ %.0fms\n" (1000. *. (Unix.gettimeofday () -. !t0)))
  in
  let show k =
    time () ;
    found := true ;
    if vars = [] then printf "Yes.\n" else
      printf "Solution found:\n" ;
    List.iter
      (fun (o,t) -> printf " %s = %a\n" o Pprint.pp_term t)
      vars ;
    printf "More [y] ? %!" ;
    let l = input_line stdin in
      if l = "" || l.[0] = 'y' || l.[0] = 'Y' then begin
        reset () ;
        k ()
      end else begin
        Term.restore_state s0 ;
        printf "Search stopped.\n"
      end
  in
    prove ~level:One ~local:0 ~timestamp:0 g
      ~success:show
      ~failure:(fun () ->
                  time () ;
                  if !found then printf "No more solutions.\n"
                  else printf "No.\n" ;
                  assert (s0 = Term.save_state ()))
