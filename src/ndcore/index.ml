
(** In this file we implement and index structure used for tabling.
  * An index represents a set of terms, in which eigenvariables may be allowed
  * but not logic variable -- since this requires suspensions.
  * The terms are abstracted over their eigenvars in the set.
  * For efficiency, the index lookup first parses the "rigid" structure of a
  * term in linear time, and extracts variables, and then takes care of the
  * equalities among these variables.
  * Currently the Nabla indices are handled as part of the rigid structure of
  * terms, which means that weakening and swapping are not supported.
  * Later, the set of nabla variables could be extracted and simplified to an
  * essential representation just like eigenvariables. *)

(** {1 Constraint management}
  * In the tree, variables are identified by uniques numbers, which I'll call
  * the VID (variable id). We could get rid of that and rely only on the order
  * in which we meet the vars in the tree, but that would involve extra
  * care when changing an algorithm (insertion/lookup or fold).
  * So at the end of a branch we have a collection of variables with VIDs,
  * and we want to store a constraint describing this collection, such that
  * two formulas satisfying the same rigid structure and map are indeed
  * logically equivalent.
  * We first get rid of VIDs, which are not necessarily [0,1,2..n], and renumber
  * variables using CIDs (constraint id) from 0 to n. In the constraint we
  * store:
  * - the maximum VID
  * - an array mapping CID to VID
  * - an array describing variable equalities: to each variable (denoted by its
  *   CID) is associated the smallest (in term of CID) equal variable.
  * - the array mapping CIDs to local timestamps. *)

type constraints = { max_vid : int ;
                     vid     : int array ;
                     eq      : int array ;
                     lts     : int array }

let dummy_var = {Term.name="";Term.lts=0;Term.ts=0;Term.tag=Term.Constant}

exception Found of int

let get_constraints bindings =
  let n = List.length bindings in
  (* Sorting might be a useless precautions since we always parse the index
   * in the same order, but it's not critical and I need the max anyway. *)
  let bindings = List.sort (fun (i,_) (j,_) -> compare j i) bindings in
  let m = match bindings with (m,_)::_ -> m | _ -> 0 in
  (* We prepare the constraints array,
   * and transform the [(int*var) list] into a more convenient [var array]. *)
  let c = {
    max_vid = m ;
    vid     = Array.make n 0 ;
    eq      = Array.make n 0 ;
    lts     = Array.make n 0 }
  in
  let v = Array.make n dummy_var in
    ignore (List.fold_left
              (fun j (i,x) ->
                 c.vid.(j) <- i ;
                 c.lts.(j) <- x.Term.lts ;
                 v.(j) <- x ;
                 j+1)
              0 bindings) ;
    ignore (List.fold_left
              (fun j (i,x) ->
                 (* [a.(i)] gets the least index which has an equal value *)
                 c.eq.(j) <-
                   begin try
                     for k = 0 to j do
                       if v.(k) = x then raise (Found k)
                     done ;
                     assert false
                   with
                     | Found k -> k
                   end ;
                 j+1)
              0 bindings) ;
    c

module ConstraintsOrdered = struct
  type t = constraints
  let compare = compare
end
module ConstraintsMap = Map.Make(ConstraintsOrdered)

let new_leaf bindings data =
  let map = ConstraintsMap.empty in
    ConstraintsMap.add (get_constraints bindings) data map

let update_leaf map bindings data =
  match data with
    | Some data -> ConstraintsMap.add (get_constraints bindings) data map
    | None -> ConstraintsMap.remove (get_constraints bindings) map

let find_leaf map bindings =
  ConstraintsMap.find (get_constraints bindings) map

(** {1 Indexing} *)

(** Patterns allow eigenvariables and nabla variables as deBruijn indices. *)
type pattern =
  | DB    of int
  | NB    of int
  | Cst   of Term.id
  | Var   of int
  | Lam   of int * pattern
  | App   of int * pattern list (* Store the length of the list *)
  | Hole

type 'a t        = 'a node list
and  'a node     = pattern list * 'a children
and  'a children = Refine of 'a t | Leaf of 'a ConstraintsMap.t

let empty = []

exception Cannot_table

let observe term = Term.observe (Norm.hnorm term)

(** [create_node bindings terms data] compiles the terms into patterns
  * and associates them a leaf containing the data.
  * Terms are expected to be reversed. *)
let create_node ~allow_eigenvar bindings terms data =
  let bindings = List.sort (fun (i,_) (j,_) -> compare i j) bindings in
  let add bindings v =
    let rec aux accu expect = function
      | (i,x)::l when i=expect -> aux ((i,x)::accu) (expect+1) l
      | l -> expect, List.rev_append accu ((expect,v)::l)
    in
      aux [] 0 bindings
  in
  let rec compile bindings term = match observe term with
    | Term.DB i -> DB i, bindings
    | Term.NB i -> NB i, bindings
    | Term.Var {Term.tag=Term.Constant;Term.name=id} -> Cst id, bindings
    | Term.Var var when allow_eigenvar && var.Term.tag = Term.Eigen ->
        let i,bindings = add bindings var in
          Var i, bindings
    | Term.Lam (i,t) ->
        let pat,bindings = compile bindings t in
          Lam (i,pat),bindings
    | Term.App (h,terms) ->
        let terms = h::terms in
        let patterns,bindings =
          List.fold_left
            (fun (pats,b) t ->
               let (p,b) = compile b t in
                 (p::pats,b))
            ([],bindings)
            terms
        in
          App (List.length terms, List.rev patterns),bindings
    | _ -> raise Cannot_table
  in
  let patterns,bindings =
    List.fold_left
      (fun (pats,binds) term ->
         let pat,binds = compile binds term in
           pat::pats,binds)
      ([],bindings)
      terms
  in
    patterns, Leaf (new_leaf bindings data)

(* [superficial_match] expects a head-normalized term. *)
let superficial_match patterns terms =
  let sub (pat,term) = match pat, Term.observe term with
    | DB i, Term.DB j
    | NB i, Term.NB j
    | Lam (i,_), Term.Lam (j,_) -> i=j
    | Cst i, Term.Var {Term.name=j;Term.tag=Term.Constant} -> i=j
    | Var _, Term.Var {Term.tag=Term.Eigen} -> true
    | App (i,_), Term.App (h,l) -> i = 1 + List.length l
    | Hole, _ -> true
    | _ -> false
  in
    List.for_all sub (List.map2 (fun a b -> a,b) patterns terms)

(* == UPDATE =============================================================== *)

(* TODO Some of these are tailrec, some waste this effort..
 *      Everything can be done tailrec using a zipper,
 *      and we'll get a flexible function allowing search and update
 *      in a single pass.
 * access : index -> term -> data option * (data -> index) * (() -> index)
 *                           found         update            delete          *)

let update ~allow_eigenvar index terms data =
  (* Update_pattern returns the list of catches and the alternative
   * corresponding to the former index in reverse order. *)
  let rec update_pattern bindings catches former_alt pattern term =
    match pattern, observe term with
      | DB i, Term.DB j when i = j ->
          (false, DB i, bindings, catches, former_alt)
      | NB i, Term.NB j when i = j ->
          (false, NB i, bindings, catches, former_alt)
      | Cst c, Term.Var {Term.name=c';Term.tag=Term.Constant} when c=c' ->
          (false, Cst c, bindings, catches, former_alt)
      | Var i, Term.Var var when allow_eigenvar && var.Term.tag=Term.Eigen ->
          (false, Var i, (i,var)::bindings, catches, former_alt)
      | App (i,patterns), Term.App (h,terms) when i = 1 + List.length terms ->
          let terms = h::terms in
          let (changed,patterns,bindings,catches,former_alt) =
            update_patterns bindings catches former_alt patterns terms
          in
          let patterns = List.rev patterns in
            assert (List.length patterns = i) ;
            (changed, App (i,patterns), bindings, catches, former_alt)
      | Lam (i,pattern), Term.Lam (j,term) when i = j ->
          let (changed,pattern,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pattern term
          in
            (changed, Lam (i,pattern), bindings, catches, former_alt)
      | Hole,_ ->
          (false, Hole, bindings, term::catches, Hole::former_alt)
      | _ ->
          (true, Hole, bindings, term::catches, pattern::former_alt)

  and update_patterns bindings catches former_alt patterns terms =
    assert (List.length patterns = List.length terms) ;
    List.fold_left2
      (fun (changed,patterns,bindings,catches,former_alt) pattern term ->
         (* Go through one pattern, enrich catches and bindings,
          * and build the updated pattern. *)
         let (changed',pattern,bindings,catches,former_alt) =
           update_pattern bindings catches former_alt pattern term
         in
           changed'||changed,pattern::patterns,bindings,catches,former_alt)
      (false,[],bindings,catches,former_alt)
      patterns
      terms
  in

  let rec update_node bindings terms (patterns,children) =
    let changed,patterns,bindings,catches,former_alt =
      update_patterns bindings [] [] patterns terms
    in
    let patterns = List.rev patterns in
    let former_alt = List.rev former_alt in
      patterns,
      if changed then
        (* The new patterns have some new holes, we separate the new and the
         * former terms by adding an intermediate index.
         * We need to compile the caught terms into patterns. *)
        match data with
          | Some data ->
              Refine [ create_node ~allow_eigenvar bindings catches data ;
                       former_alt, children ]
          | None -> raise Not_found
      else
        (* The terms were fully matched by the patterns,
         * the new [patterns] is the same as the former one,
         * the update gets propagated deeper without changing anything here. *)
        match children with
          | Refine index ->
              Refine (update_index bindings
                        (List.map Norm.hnorm (List.rev catches)) [] index)
          | Leaf map ->
              assert (catches = []) ;
              Leaf (update_leaf map bindings data)

  (* Update an index, i.e. an (unordered) list of alternative nodes. *)
  and update_index bindings terms index' = function
    | [] ->
        begin match data with
          | Some data ->
              (create_node ~allow_eigenvar
                 bindings (List.rev terms) data)::index'
          | None -> raise Not_found
        end
    | node::index ->
        if superficial_match (fst node) terms then
          (update_node bindings terms node)::index@index'
        else
          update_index bindings terms (node::index') index
  in
    update_index [] (List.map Norm.hnorm terms) [] index

let add ?(allow_eigenvar=true) index terms data =
  update ~allow_eigenvar index terms (Some data)

(* == FIND ================================================================= *)

(* Filter a term through a pattern, raise Not_found on mismatch,
 * return the list of bindings and the reversed list of catches. *)
let rec filter bindings catches pattern term =
  match pattern, observe term with
    | DB i, Term.DB j
    | NB i, Term.NB j when i=j -> bindings,catches
    | Cst i, Term.Var {Term.name=j;Term.tag=Term.Constant} ->
        if i=j then bindings,catches else raise Not_found
    | Var i, Term.Var var ->
        if var.Term.tag = Term.Eigen then
          (i,var)::bindings,catches
        else
          raise Not_found
    | Lam (i,pattern), Term.Lam (j,term) ->
        if i=j then
          filter bindings catches pattern term
        else
          raise Not_found
    | App (i,patterns), Term.App (h,l) ->
        if i = 1 + List.length l then
          filter_several bindings catches patterns (h::l)
        else
          raise Not_found
    | Hole,_ -> bindings,term::catches
    | _ -> raise Not_found

(* Same as [filter], returns the catches in reverse order. *)
and filter_several bindings catches patterns terms =
  List.fold_left2
    (fun (bindings,catches) pattern term ->
       filter bindings catches pattern term)
    (bindings,catches)
    patterns terms

let rec find bindings index terms =
  match index with
    | [] -> raise Not_found
    | (patterns,children)::index ->
        if superficial_match patterns terms then
          let bindings,catches = filter_several bindings [] patterns terms in
            match children with
              | Leaf map ->
                  assert (catches = []) ;
                  find_leaf map bindings
              | Refine index ->
                  find bindings index (List.map Norm.hnorm (List.rev catches))
        else
          find bindings index terms

let find index terms =
  try Some (find [] index (List.map Norm.hnorm terms)) with _ -> None

(* == FOLD ================================================================== *)

(* We use some kind of multi-locations zippers *)

module type MZ_t =
sig
  type t
  val empty : t
  val refine : t -> pattern list -> t
  val zip : Term.term array -> t -> Term.term list
end

module MZ : MZ_t =
struct

  type item =
    | ZNB of int | ZDB of int  | ZCst of Term.id | ZVar of int
    | ZLam of int | ZApp of int
    | ZHole

  type t = item list list

  let arity = function
    | ZDB _ | ZNB _ | ZCst _ | ZVar _ -> 0
    | ZHole | ZLam _ -> 1
    | ZApp n -> n

  let arity = function
    | [] -> assert false
    | row::_ -> List.fold_left (+) 0 (List.map arity row)

  let empty = []

  let compile_step pats =
    let row,subpats =
      List.fold_left
        (fun (row,subpats) -> function
           | DB i  ->  (ZDB i)::row, subpats
           | NB i  ->  (ZNB i)::row, subpats
           | Cst c -> (ZCst c)::row, subpats
           | Var i -> (ZVar i)::row, subpats
           | App (n,l) -> (ZApp n)::row, List.rev_append l subpats
           | Lam (n,p) -> (ZLam n)::row, p::subpats
           | Hole -> ZHole::row, Hole::subpats)
        ([],[])
        pats
    in
      List.rev row,
      List.rev subpats

  let rec refine acc patterns =
    if List.for_all ((=) Hole) patterns then acc else
      let row,sub = compile_step patterns in
        refine (row::acc) sub

  let split_at_nth l n =
    let rec aux before l n =
      if n = 0 then List.rev before, l else
        match l with
          | h::l -> aux (h::before) l (n-1)
          | _ -> assert false
    in aux [] l n

  let zip table mz =
    let zip_step terms = function
      | ZDB i  -> Term.db i, terms
      | ZNB i  -> Term.nabla i, terms
      | ZCst c -> Term.const c 0, terms
      | ZVar i -> table.(i), terms
      | ZApp n ->
          begin match split_at_nth terms n with
            | (h::tl),terms ->
                Term.app h tl, terms
            | _ -> assert false
          end
      | ZLam n ->
          begin match terms with
            | h::terms -> Term.lambda n h, terms
            | _ -> assert false
          end
      | ZHole ->
          begin match terms with
            | h::terms -> h, terms
            | _ -> assert false
          end
    in
    let rec zip terms row =
      let out,terms =
        List.fold_left
          (fun (out,terms) item ->
             let t,terms = zip_step terms item in
               t::out,terms)
          ([],terms)
          row
      in
        assert (terms = []) ;
        List.rev out
    in
      List.fold_left zip [] mz

end

let iter index f =
  let rec iter_children mz = function
    | Leaf map ->
        ConstraintsMap.iter
          (fun c v ->
             let table = Array.make (c.max_vid+1) (Term.db 0) in
             let l = ref [] in
               for i = 0 to Array.length c.eq - 1 do
                 table.(c.vid.(i)) <-
                   if c.eq.(i) = i then
                     Term.fresh 0
                   else
                     table.(c.vid.(c.eq.(i))) ;
                 if c.eq.(i) = i then
                   l := table.(c.vid.(i)) :: !l
               done ;
               let head = Term.fresh 0 in
               let t = Term.app head (MZ.zip table mz) in
               let l = List.rev !l in
               let t =
                 List.fold_left
                   (fun t v -> Term.abstract_var v t)
                   t
                   l
               in
                 f (Term.abstract_var head t) v)
          map
    | Refine i -> iter_index mz i

  and iter_node mz (patterns,children) =
    iter_children (MZ.refine mz patterns) children
  and iter_index mz = List.iter (iter_node mz) in

    iter_index MZ.empty index
