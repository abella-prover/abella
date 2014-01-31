(****************************************************************************)
(* Schema Extension                                                         *)
(* Copyright (C) 2013 Savary Chaudhuri                                      *)
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

open Term
open Metaterm
open Typing
open Abella_types
open Printf
open Prover
open Extensions
open Schema_types


let slexbuf = ref (Lexing.from_string "")


(* name of schema associated to
    - arrity of the each clauses 
    - list of clauses, each consisting of
          * list of logic variables used in the clause
          * list of nominal vars
          * list of terms of type o *)

type schemas = (id * (int * (((id*ty) list)*((id*ty) list)*((term option) list)) list)) list
let schemas : schemas ref = ref []




let add_schema name schema =
 schemas := (name, schema)::!schemas


let get_schema name =
 try List.assoc name !schemas 
 with Not_found -> failwith (sprintf "Block %s undefined." name)

(* May contain the name of the schema currently being defined *)
let saveSchema = ref None

let try_del_schema () =
begin 
  match (!saveSchema) with
  | None -> ()
  | Some id -> 
      let ts = List.remove_assoc id (!schemas) in
      schemas := ts
end

(* General Toolbox *)

(* return true if all the members of l are None *)
let rec all_none l =
  let bl = List.map Option.is_none l in 
  List.fold_left (fun b cb -> b && cb) true bl



let fail_if_false b =
if b then () else raise (Failure "false") 


let rec remove_nones l =
 match l with
 |  None::l' -> (remove_nones l')
 | (Some o)::l' -> o::(remove_nones l')
 | [] -> []

    
(* return the first non-empty element in a list of option *)
let rec find_first l =
 match l with
 |  None::l' -> find_first l'
 | (Some o)::l' -> o
 | [] -> raise Not_found

(* split l:('a ,'b,'c) list into ('a list, 'b list, 'c list) *)
let split3 l = 
List.fold_right (fun (a,bl,cl) (ca, cb, cc) -> (a::ca,bl::cb, cl::cc)) l ([],[],[])

(* on int n and string s, returns ["s1", ..., "sn"]  *)
let rec string_count n s = begin match n with
|  0 -> []
|  n -> List.append (string_count (n-1) s) [s^(string_of_int n)]
end

(* returns the position at which s first occurs in list l *)
let rec mem_pos s l = begin match l with
| h::t -> if h = s then 1 else 
              (mem_pos s t)+1
| [] -> failwith ("in mem_pos, "^s^" not found in list")
end


let rec append_uni_assocs l1 l2 =
begin match l2 with
|  [] -> l1
| (idh,tyh)::l2' -> 
    let l3 = append_uni_assocs l1 l2' in
    if (List.mem_assoc idh l3) then
      (let ty = List.assoc idh l3 in
      if ty = tyh then
	l3
      else
	failwith ("Coudn't determine the type of "^idh)
	)
    else
      (idh,tyh)::l3
end


let rec split_n_from_list n l =
begin match (n,l) with
| (n, h::tl) ->  
    let (f,t) = split_n_from_list (n-1) tl in
     (h::f, t)
| (0, []) -> ([],[])
|  _ -> failwith "in split_n_from_list, coudln't remove n element" 
end


(* similar to List.unique except for keys in an assoc list *)
let rec rem_rep_pairs idfool = begin match idfool with
| (id,foo)::idl' -> 
    if (List.mem_assoc id idl') then idl' else ((id,foo)::idl')
|  [] -> []
end 




(* Schema toolbox *)

let check_noredef ids =
  let (_, ctable) = !sign in
    List.iter (
      fun id -> if List.mem id (List.map fst ctable) then
        failwith (sprintf "%s is already defined" id)
    ) ids


(* returns a list of n fresh hypothesis name, using s as naming hint *)
let make_n_fresh_hyp n s = 
  let (_ , hs) = List.fold_right (fun  hn (hypctx, fns) -> 
    let fhn = fresh_name hn  hypctx in
    ((fhn, ())::hypctx , fhn::fns)) (string_count n s) ((List.map (fun h -> (h.id, ())) sequent.hyps),[])  in
  hs


(* return the name and type of every variables of tag "tag" occuring in term "tm" *)
let get_vars tag tm =
  List.map (fun v -> (Term.(v.name), v.ty)) (find_vars tag [tm])



let logic_var ?(ts=(max_int-1)) s ty =
  var Logic s ts ty

let tyctx_to_logical_ctx tyctx =
  List.map (fun (id, ty) -> (id, logic_var id ty)) tyctx




let rec get_head_id tm =
  begin match observe (hnorm tm) with
  | App ( t , _ ) -> get_head_id t
  | Var v -> Term.(v.name)
  | _ -> invalid_arg "Unexpected term in get_head_id"
  end


let rec rename_ids_in_idtys sub idtys = 
begin match idtys with
|  (idh,tyh)::idtys' -> let sidtys' = rename_ids_in_idtys sub idtys' in  if
    (List.mem_assoc idh sub) then (List.assoc idh sub, tyh)::sidtys' else (idh,tyh)::sidtys'
|  [] -> []
end



let rec rename_ids_in_term sub tm = 
match observe tm with
| Var v -> 
    if (List.mem_assoc Term.(v.name) sub) then (var (v.tag) (List.assoc Term.(v.name) sub) (v.ts) (v.ty)) else tm
| App (th, tt) -> 
    let th' = rename_ids_in_term sub th in
    let tt' = List.map (rename_ids_in_term sub) tt in
     app th' tt'
| Lam(idtys,t) -> 
    let sub = List.fold_left (fun sub' (id,ty) -> 
                                  List.remove_assoc id sub') sub idtys in
    let t' = rename_ids_in_term sub t in
     lam idtys t'
|  _ -> tm




let rec type_vars_in tm ty sign =
begin match observe tm with 
| Var v -> let vn = Term.(v.name) in
         begin try 
	   let ety = lookup_const !sign vn in
	   if ty <> ety then
	     failwith ("in type_vars_in, constant "^(term_to_string tm)^" has type "^(ty_to_string ety)^" instead of expected type "^(ty_to_string ty)^". \n")
	   else
	     []
         with _ -> 
            [(Term.(v.name), ty) ]
	 end
| App (th, tt) ->
    begin try 
      let Ty(tys,bty)  = lookup_const !sign (term_to_string th) in
      let n = List.length tt in
      if n <= (List.length tys) then
	let (tys',_) = split_n_from_list n tys in
	let idtysl = List.map (fun (tm,ty) -> type_vars_in tm ty sign) (List.combine tt tys') in
	List.flatten idtysl
      else
      failwith ("in type_vars_in, term "^(term_to_string tm)^" has a function applied to too many arguments")
    with _ -> failwith ("in type_vars_in, can't type "^(term_to_string tm)^"%s. \n") end
| Lam (idtys, t ) -> 
       let Ty(tys,bty) = ty in
       let n = List.length idtys  in
       if n >= (List.length tys) then
	 let (_,tys') = split_n_from_list n tys in
	 type_vars_in t (Ty(tys', bty)) sign 
       else
	 failwith ("in type_vars_in, "^(term_to_string tm)^" doesn't fit type "^(ty_to_string ty)^". \n" )
| DB i  -> []
|  _ -> invalid_arg ("in type_vars_in, unhandled "^(term_to_string tm)^". \n")
end




(* SCHEMA *)

(* verify that each variable appearing in the substitution is only bound to a single term *)
let rec isPSub' sub c =
begin match sub with
| (pid,tm)::sub' -> 
    if (List.mem_assoc pid c) then 
      begin if term_to_string (List.assoc pid c) = (term_to_string tm)
      then isPSub' sub' c
      else false end
    else
      (isPSub' sub' ((pid,tm)::c))
| [] -> true
end

let rec isPSub sub = isPSub' sub []



(* verify if term "tm" matches pattern "ptn", returns "(b,sig)" where "b" is the answer, and "sig" a pattern substitution for which tm = (sig) ptn *)
let rec patternMatch tm ptn  = 
  let (_,ctable) = !sign in
 begin match observe (hnorm tm), observe (hnorm ptn) with
 | Var v, Var pv -> 
       begin match (List.mem_assoc (term_to_string tm) ctable, List.mem_assoc (term_to_string ptn) ctable) with
      | true, true -> if (term_to_string tm) = (term_to_string ptn) then (true,[]) else (false,[]) (* both are the same constant *)
      | false, false -> (true, [(Term.(pv.name),tm)])
      |	 _ , _ -> (false, [])
       end
 |  App(th,tt), App(pth, ptt) ->
     let (bh, subh) = patternMatch th pth in
     if bh then 
       let rl = List.map (fun (ctm,cptn) -> patternMatch ctm cptn) (List.combine tt ptt) in
       let (bl, subl) = List.split rl in
       begin if (List.fold_left (fun bt ct -> bt && ct) true bl) then
	 let sub = List.append subh (List.flatten subl) in
	 (* substitution *)
	 begin if isPSub sub then (true, sub) else (false, []) end
       else (false, [])
       end
     else 
       (false, [])
 | App(th,tt), Var pv ->
   (* check if v is exists bound, then true, else [nabla bound or constant] false *)
      if Term.(pv.tag) = Logic then (true, [(Term.(pv.name), tm)]) else (false,[])
 | Lam(idtys,tm'), Lam(pidtys,ptn') ->  
      patternMatch tm' ptn' 
 | DB i, DB j ->  if (i = j) then (true, []) else (false ,[])
 |  _ , _ -> (false, [])
 end


(* returns a list of (bool * (id * id) list)  with, for each pattern in bls, if t could match the pattern, and if it is the case, a substitution s.t. the term = @sub pat *)
let rec instOfPats t bls = 
List.map (patternMatch t) bls
    

let rec seqIdTerm id t nl = 
   begin match observe t with
   | App (th,tt) -> 
     let (nl',th') = seqIdTerm id th nl in
     let (nl'',tt') = (List.fold_right ( fun t (nl,tl) -> 
                                     let (nl',t') = seqIdTerm id t nl in
                                        (nl', t'::tl)) tt (nl',[])) in
    (nl'', app th' tt')
   | Var v -> 
 begin if Term.(v.tag = Nominal) then
        (nl,Term.(var Constant "" max_int (Ty([],"err"))))
   else
     let i = nl+1 in
     let vn = id^(string_of_int i) in
     (i, var v.tag vn v.ts v.ty) end
   | _ -> invalid_arg (sprintf "unexpected %s in seqIdTerm" (term_to_string t))
   end






let rec seqNameTerm t nl v c = 
   let (_,ctable) = !sign in
   begin match observe (hnorm t) with
   | App (th1,tt1) ->  
   begin if List.mem_assoc (term_to_string th1) ctable then 
   let (nl,th1') = seqNameTerm th1 nl v c in
   let (nl,tt1') = (List.fold_right (fun (t1) (nl, t1l) ->  
                             let (nl',t1') =  seqNameTerm t1 nl v c in
                                 (nl', t1'::t1l))
            (tt1) (nl,[])) in
   (nl, (app  th1' tt1'))
   else 
     (nl+1, logic_var (c^(string_of_int nl))  ((Ty([],"err"))))
   end 
   | Var v1 ->
       if (Term.(v1.name) = v) || List.mem_assoc Term.(v1.name) ctable then 
	 (nl,t)
       else
	 (nl+1, logic_var (c^(string_of_int nl))  ((Ty([],"err"))))
   | Lam (idtys1, tm1') -> 
      let (nl, tu1') =  seqNameTerm tm1'  nl v c in
      (nl, lambda idtys1 tu1')
   | DB _ -> (nl, t)
   | _ ->  
 invalid_arg (sprintf "unexpected %s in seqNameTerm" (term_to_string t)) 
   end


(* Returns an integer "n" and two copies of T, one with its logic variables replaces by a sequence of "Ai"s and the other with "Bi"s, numbered for i=1 to n *)
let uniteTerms t v =
  let n,t1 = seqNameTerm t 1 v "A" in
  let _,t2 = seqNameTerm t 1 v "B" in
    (n-1,t1,t2)
 
   

let rec pairwiseEqual t1 t2 = 
  let (_,ctable) = !sign in
  begin match (observe (hnorm t1), observe (hnorm t2)) with
  | Var v1, Var v2 -> 
      let v1n = Term.(v1.name) in
      let v2n = Term.(v2.name) in
      if v1n = v2n   then
        if (List.mem_assoc v1n ctable) then
	   []
	else
	   [v1n]
      else 
	[]
  | App (t1h,t1l), App(t2h,t2l) -> 
      begin try 
      let varll = List.map (fun (t1,t2) -> pairwiseEqual t1 t2) (List.combine (t1h::t1l) (t2h::t2l)) in
      let varl = List.flatten varll in
       List.unique varl
      with Invalid_argument e -> [] end
  | Lam(idtys1, t1') , Lam(idtys2, t2') ->
      pairwiseEqual t1' t2'
 |  _ , _ ->  []
  end



(* Make one fresh definition for each pairs of exists, nabla bound variable *)
(*exists bound variables, nabla bound variables, id paired with their type *)
let rec makeFreshGeneric' tys1 ty2  =
  begin match tys1 with
  | ty1::tys1p ->
      let ty1str = (ty_to_string ty1) in
      let ty2str = (ty_to_string ty2) in
      let freshname = "fresh_"^ty2str^"_in_"^ty1str in
      if H.mem defs_table freshname then 
	makeFreshGeneric' tys1p ty2
      else 
      let freshstr = "Define "^freshname^" : "^ty2str^" -> "^ty1str^" -> prop by \n nabla n, "^freshname^" n X. \n" in
      let restOf = makeFreshGeneric' tys1p ty2  in
      freshstr^restOf
  | [] -> ""
  end


(* assumes there is no repetition in tys1,tys2 *)
let rec makeFreshGeneric tys1 tys2 =
  begin match tys2 with
  | ty2::tys2p -> 
      let curFresh = makeFreshGeneric' tys1 ty2 in
      let restOf = makeFreshGeneric tys1 tys2p in
       curFresh^restOf
  | [] -> ""


  end
(* assumes there is no repetition in tys *)
let rec makeNameGeneric tys = 
begin match tys with
| ty::tys' ->
    let tystr = ty_to_string ty in
    let namename = "name_"^tystr in
    begin if H.mem defs_table namename then
      makeNameGeneric tys' 
    else
      let curName = "Define "^namename^" : "^tystr^" -> prop by \n nabla x, "^namename^" x.\n" in
      let restOf = makeNameGeneric tys' in
      curName^restOf
    end
| [] -> ""
end


(* Make one prune lemma for each nabla bound variable *)
(* nabla bound variables, id paired with their type *)
(* assumes there is no repetition in tys *)
let rec makePruneGeneric tys =
  begin match tys with
  | ty::tysp -> 
      let tystr = ty_to_string ty in
      let prnname = "member_prune_"^tystr in
      if List.mem_assoc prnname !lemmas  then 
        makePruneGeneric tysp 
      else
	let prnstr = "Theorem "^prnname^" : forall G E, nabla (n:"^tystr^"),member (E n) G -> (exists E', E = x\\E').\n" in
	let prnprf = "induction on 1. intros. case H1. search. apply IH to H2. search.\n" in
	let restOf =  makePruneGeneric tysp in 
	prnstr^prnprf^restOf
  |  [] ->  ""
end

let rec makeBlockGeneric tys1 tys2 =
  let tys1 = List.unique tys1 in
  let tys2 = List.unique tys2 in
  let freshDefs = if tys1 = [] then makeNameGeneric tys2 else makeFreshGeneric tys1 tys2 in
  let pruneDefs = makePruneGeneric tys2 in
   freshDefs^pruneDefs





let rec one_fresh (id1,ty1) idtys2 = 
  begin match idtys2 with
 | (id2,ty2)::idtys2' ->
     let fresh = " fresh_"^(ty_to_string ty2)^"_in_"^(ty_to_string ty1)^" "^id2^" "^id1^" " in 
     let rst = one_fresh (id1,ty1) idtys2' in
     fresh::rst
 | [] -> []
  end

(* idtys1:(id*ty) list
   idtys2:(id*ty) list
   return a str list of the assumption that, for each var id in idtys1, every id in idtys2 is fresh in it.
*)
let rec all_fresh idtys1 idtys2 = 
  begin match idtys1 with
  | idty1::idtys1' -> 
      List.append (one_fresh idty1 idtys2) (all_fresh idtys1' idtys2)
  | [] -> []
end

(* idtys:(id*ty) list
   returns a str list of the name assumption for each id in idtys. 
*)
let rec all_name idtys =
begin match idtys with
| (id,ty)::idtys' -> ("name_"^(ty_to_string ty)^" "^id)::(all_name idtys')
| [] -> []
end


(* verifies that t1 and t2 are of the form *)
(* t1 = ctx G1 ... GN *)
(* t2 = member E Gi *)
(* verifies that ctx is a defined schema *)
(* output (ctx, i, E) *)
let member_of_ith t1 t2 =
  begin match observe t1, observe t2 with
  | App (t1h,t1l), App(t2h,t2l) -> if ((term_to_string t2h) = "member") then
      let t1l' = List.map (get_head_id) t1l in 
      let gi = get_head_id (List.hd (List.tl t2l)) in 
      let schName = term_to_string t1h in
      if (List.mem_assoc schName !schemas) then () else failwith ("Schema: "^schName^" is not the name of a defined schema");
       ( schName ,(mem_pos gi t1l'), List.hd t2l)
  else failwith "Schema: hypothesis should be of the form 'member E G'. "
  | _ -> invalid_arg "Shema: hypothesis should be of the given form."
  end


(* if Some tm, unify with previous tm' in the list if there is, otherwise add to list
   if None, then clause couldn't have introduced formulas to other projections sharing the same projection variable, so if another constraints sharing the same variables have introduced a constraints, remove all constraints for that clause. *) 
let rec makeClauseConstrain idtm const = 
begin match idtm with
| (id, Some tm)::idtm' ->
    if List.mem_assoc id const then
      let tm' = List.assoc id const in
      fail_if_false (Unify.try_right_unify tm tm');
      makeClauseConstrain idtm' const
    else
      makeClauseConstrain idtm' ((id,tm)::const)
| (id, None)::idtm' ->
    let const' = makeClauseConstrain idtm' const in
     if List.mem_assoc id const' then
       []
     else
       const'
| [] -> const
end


(* ids: name of the projections of the schema
   cls: list of (term option lists), for each clause of the schema. *)
let rec proClConst ids cls =
  begin match cls with
  | (tts)::cls' -> 
      let res = proClConst ids cls' in
      let idtts = List.combine ids tts in
      begin try 
	let clConst = makeClauseConstrain idtts [] in
	clConst::res
      with _ ->  failwith "Schema: in proClConst, failed to unify projection constraints. \n" 
      end 	
  | [] -> []
  end



(* verify if the given clauses matches the list of constraints, fail if it doesn't, o.w. return unit 

 const: (id*tm) list, list of contraints
 idtms: (id*tm) list, terms from the clause's projection paired with their projections variable *)
let rec clMatchesConst constl idtms =
begin match idtms with
| (id,tm)::idtms' ->
    if (List.mem_assoc id constl) then
      let tm' = List.assoc id constl in
      let (b,_) = patternMatch tm' tm  in
      if b then
	clMatchesConst constl idtms'
      else
	failwith "cl doesn't match the given constL"
    else
      clMatchesConst constl idtms'
| [] -> ()
end


(* constl: (id*tm) list, constraints from the clause being checked
   idts:id list, name of the projection for the destination schema
   cltms: (term option list) list, clauses of the destination schema
*)
let rec findMatchingCls constlO ids cltms = 
  begin match cltms with
  | tms::cltms' -> 
      let idtms = List.combine ids tms in
      let constlD = makeClauseConstrain idtms [] in
      begin try 
	if constlD = [] then
	  failwith "next!"
	else
	  clMatchesConst constlO constlD
      with _ ->  findMatchingCls constlO ids cltms' end
  | [] -> failwith "Schema: No clauses the given format for the projection being built. \n"
  end


(* clConst:((id*tm) list) list, constraints created from each of the clauses of the origin schema
   idts:id list, name of the projection for the destination schema
   cltms: (term option list) list, clauses of the destination schema
*)
let rec checkProMatches clConst ids cltms = 
  begin match clConst with
  | (constl)::clConst' ->
      checkProMatches clConst' ids cltms;
      findMatchingCls constl ids cltms
      
  | [] -> ()
  end



let make_schema_def schName arr bids = 
	    let schTy = (str_repeat arr " olist ->")^" prop" in
	    let blids = List.map (fun (a,b,l) -> l) bids in 
	    let clstrl = List.map (fun e ->
		 List.fold_left (fun (i,defl,defr) -> fun otm -> 
		   begin match otm with 
		   | None -> (i+1, defl^" G"^(string_of_int i), defr^" G"^(string_of_int i))
		   | Some tm -> (i+1,defl^" (("^(term_to_string tm)^") :: G"^(string_of_int i)^")", defr^" G"^(string_of_int i)) 
		   end ) (1, schName, schName)  e) blids in
	    begin match List.length blids with
	    |  0 -> "Define "^schName^":"^schTy^" by \n"^schName^(str_repeat arr " nil")^"."
	    |  _ -> "Define "^schName^":"^schTy^" by \n"^schName^(str_repeat arr " nil")^";\n"^(String.concat ";\n" (List.map (fun ((_,b,_),(_,d,e)) -> 
		let (nid,nty) = List.split b in
		if b = [] then 
		  sprintf "%s := %s "  d e
		else 
		  sprintf "nabla %s , %s := %s" (String.concat " " nid) d e) (List.combine bids clstrl)))^"." end 



let make_sync_clause i ((a,b,l),(it,sub)) = 
  let substr = List.map (fun (id,tm) -> (id, (term_to_string tm))) sub in
  begin match it with
  | true ->
      let ( j ,cl,idtys1,idtys2, eit,nit ) = 
	List.fold_left (fun (j,cstr,idty1,idty2, eit , nit ) -> fun otm ->
	  begin match otm with
	  | None -> 
	      (j+1,cstr, idty1,idty2, eit, nit)
	  | Some cbl -> 
	      let c = get_vars Logic cbl in
	      let d = get_vars Nominal cbl in
	      if (j = i) then
		(j+1,cstr, idty1, idty2, rename_ids_in_idtys substr c, rename_ids_in_idtys substr d)
	      else 
		let s = sprintf "member (%s) G%d" (term_to_string (rename_ids_in_term substr cbl)) j in
		let c' = List.filter (fun (id,ty) -> not (List.mem_assoc id sub)) c in
		
		let d' = List.filter (fun (id,ty) -> not (List.mem_assoc id sub)) d in 
		(j+1,s::cstr, (List.append c' idty1),(List.append d' idty2), eit, nit) end) (1,[],[],[], [], []) l in
      let idtysa = rem_rep_pairs idtys1 in
      let idtysb = rem_rep_pairs idtys2 in
      let (ida',tya) = List.split idtysa in
      let (idb',tyb) = List.split idtysb in
      let eBidtyl = (List.append idtysa eit) in
      let nBidtyl = (List.append idtysb nit) in
      let freshl = if eBidtyl = [] then all_name nBidtyl else all_fresh eBidtyl nBidtyl in
      let ab = List.append ida' idb' in
      if ab = [] then "("^(String.concat " /\\ " (List.append cl freshl))^")" else
      sprintf "(exists %s, %s)" (String.concat " " ab) (String.concat " /\\ " (List.append cl freshl))
  | false -> ""
  end


(* ids: (a,b, (c,d,e) list) list *)
(* ground on the ith projection of the context *)
(* fresh on a b *)
(* for every (c,d,e) other than the ith, member l(c,d,e) Gjth *)
let make_sync_stmt i id arr ids ads tm = 
  let lfvl = get_vars Logic tm in
  let nfvl = get_vars Nominal tm in
  let (fvl,_) = List.split (List.append lfvl nfvl) in
  let fvstr = String.concat " " fvl in
  let clstrl = List.map  (make_sync_clause i) (List.combine ids ads) in
  let clstrl = List.filter (fun s -> not (s = "")) clstrl in
    let ctxgl =  string_count arr "G" in
    let ctxg = String.concat " " ctxgl in
    sprintf "forall %s %s, %s -> member (%s) G%d -> %s. \n" fvstr ctxg (id^" "^ctxg) (term_to_string tm) i (String.concat " \\/ \n" clstrl)




let make_sync_prf ads = 
  let hs = make_n_fresh_hyp  5 "Hinv" in
let clstrl = List.map (
  fun (b,_) -> if b then 
    (sprintf "%s: case %s. search. apply %s to %s %s. search." (List.nth hs 4) (List.nth hs 2) (List.nth hs 0) (List.nth hs 3) (List.nth hs 4))
  else 
    (sprintf "%s: case %s. apply %s to %s %s. search." (List.nth hs 4) (List.nth hs 2) (List.nth hs 0) (List.nth hs 3) (List.nth hs 4))
      ) ads in
 (sprintf "%s: induction on 1. intros %s %s. %s: case %s. %s: case %s.\n" (List.nth hs 0) (List.nth hs 1) (List.nth hs 2) (List.nth hs 3) (List.nth hs 1) (List.nth hs 4) (List.nth hs 2))^(String.concat "\n" clstrl)
 


(* ids: (a,b, (c,d,e) list) list *)
(* ground on the ith projection of the context *)
(* fresh on a b *)
(* for every (c,d,e) other than the ith, member l(c,d,e) Gjth *)
(* for ith (c,d,e), E = l(c,d,e) *)
let make_inv_stmt i id arr ids  =
    let clstrl = List.map (fun (idtya,idtyb,l) ->
                       let otmi = List.nth l (i-1) in
		       begin match otmi with
		       | None -> "" (* i couldn't have been introduced by this clause *)
		       | Some _ -> 
                       let (j,cl) = 
			 List.fold_left (fun (j,cstr) -> fun otm -> 
			   begin match otm with 
			   | Some c -> 
			       let s = begin if j = i then
				 sprintf "E = (%s)" (term_to_string c) 
			       else
				 sprintf "member (%s) G%d" (term_to_string c) j
			       end in
			       (j+1,s::cstr) 
			   | None -> 
			       (j+1,cstr)
			   end) (1,[]) l in
		       let (a,_) = List.split idtya in
		       let (b,_) = List.split idtyb in
		       let freshl = if a = [] then all_name idtyb else all_fresh idtya idtyb in
		       let ab = List.append a b in
		       if ab = [] then "("^(String.concat " /\\ " (List.append cl freshl))^")" else
   sprintf "(exists %s, %s)" (String.concat " " (List.append a b)) (String.concat " /\\ " (List.append cl freshl)) end) ids in
   let clstrl = List.filter (fun s -> not (s = "")) clstrl in
   let ctxgl =  string_count arr "G" in
    let ctxg = String.concat " " ctxgl in
    sprintf "forall E %s, %s -> member E G%d -> %s. \n" ctxg (id^" "^ctxg) i (String.concat " \\/ \n" clstrl)


(* i:int number of clause in the schema *)
let make_inv_prf i =
  let hs = make_n_fresh_hyp  6 "Hinv" in
  let bsl = if i < 2 then " search. \n" else " case "^(List.nth hs 5)^" ."^(str_repeat i " search.")^" \n" in
  (sprintf "%s: induction on 1. intros %s %s. %s : case %s. case %s." (List.nth hs 0) (List.nth hs 1) (List.nth hs 2) (List.nth hs 3) (List.nth hs 1) (List.nth hs 2))^(str_repeat i (sprintf " %s : case %s. search. %s: apply %s to %s %s. %s" (List.nth hs 4) (List.nth hs 2) (List.nth hs 5) (List.nth hs 0) (List.nth hs 3) (List.nth hs 4) bsl))


let rec safeUniqueGround mts ads cvar =
begin match (mts, ads) with
| (cmts::mts', (false,_)::ads') -> 
    let (b,rel) = (safeUniqueGround mts' ads' cvar) in
     (b, rel)
| ((tm)::mts', (true,sads)::ads') -> 
    let (idl,tml) = List.split sads in
    let tmstrl = List.map term_to_string tml in
    let sads' = List.combine tmstrl idl  in
    begin if List.mem_assoc cvar sads' then
      let blid = List.assoc cvar sads' in
      let nvars = get_vars Nominal tm in
        if List.mem_assoc blid nvars then
	   let (b,rel) = (safeUniqueGround mts' ads' cvar) in
	    (b, blid::rel)
	else
	  let _ = (printf "ground fails(1) on %s, %s assoc with %s . \n" (term_to_string tm) cvar blid) in (false, [])
    else
      let _ = (printf "ground fails(2) on %s, no assoc for %s . \n" (term_to_string tm) cvar) in (false, [])
    end 
| ([],[]) -> (true, [])
|  _ -> invalid_arg "Schema: Unexpected in safeUniqueGround"
end 

(* mts:block list for the right projection of the schema
   ads:(bool, ?, ?) list, says which clause matches the hypothesis
   varl:str list, list of variables on which we can potentially ground the uniqueness theorem *)
let rec safeUniqueGrounds mts ads varl = 
begin match varl with
| cvar::varl' -> 
    let (b,rel)  = safeUniqueGround mts ads cvar in
    if b then (cvar, rel) else safeUniqueGrounds mts ads varl'
| [] -> failwith "Schema: Can't ground unique theorem for given assumption"
end



(* id:str, name of the schema
   tm1:term, 1st version of the term on which the uniqueness theorem is based 
   tm2:term, 2nd version ...
   nl:int, number of variables being asserted equal in tm1 and tm2
   arr:int, number of projections of the schema id
   gi:int, projection of schema id to which tm1 and tm2 belongs
   gv:str, variables on which the uniqueness theorem is ground
*)
let make_uni_stmt id tm1 tm2 nl arr gi gv =
    let idsG =  string_count arr "G" in
    let idsA = string_count nl "A" in
    let idsB = string_count nl "B" in
  let eqstrl = List.map (fun (a,b) -> a^" = "^b) (List.combine idsA idsB) in
  "forall "^gv^" "^(String.concat " " (List.append (List.append idsG idsA) idsB))^" , "^id^" "^(String.concat " " idsG)^" -> member ( "^(term_to_string tm1)^") G"^(string_of_int gi) ^" -> member ("^(term_to_string tm2)^") G"^(string_of_int gi) ^" -> "^(String.concat " /\\ " eqstrl)^" ." 



(* id:str, name of the schema
   mts:(id*ty list,id*ty list, uterm) list, list of blocks for schema id
   ads:boolean list, ith is if the ith block of mts matches 
*)
 let make_uni_prf id mts ads = 
  let hs = make_n_fresh_hyp  7 "Hinv" in
  let h1 =   (sprintf "%s: induction on 1. intros %s %s %s. %s: case %s. case %s.\n" (List.nth hs 0) (List.nth hs 1) (List.nth hs 2) (List.nth hs 3) (List.nth hs 4) (List.nth hs 1) (List.nth hs 2)) in
  let h2l = List.map (fun (tm,b) -> 
   if b then
     let idtys2 = get_vars Nominal tm in
     let (id2,ty2) = List.hd idtys2 in  
  (sprintf "%s: case %s. %s: case %s. search. apply member_prune_%s to %s.\n %s: case %s. apply member_prune_%s to %s. apply %s to %s %s %s. search." (List.nth hs 5) (List.nth hs 2) (List.nth hs 6) (List.nth hs 3)(ty_to_string ty2) (List.nth hs 6) (List.nth hs 6) (List.nth hs 3) (ty_to_string ty2) (List.nth hs 5) (List.nth hs 0) (List.nth hs 4) (List.nth hs 5) (List.nth hs 6))
  else  (sprintf "%s:case %s. %s: case %s. apply %s to %s %s %s. search." (List.nth hs 5) (List.nth hs 2) (List.nth hs 6) (List.nth hs 3) (List.nth hs 0) (List.nth hs 4) (List.nth hs 5) (List.nth hs 6))
) (List.combine mts ads) in
  h1^(String.concat "" h2l)



let make_proj_stmt schNameO schOs schNameD schDs = 
let schOb = List.unique schOs in
let schDnews = List.filter (fun p -> not (List.mem p schOs)) (List.unique schDs) in
let exB = 
  begin if schDnews = [] then
    ""
  else
    "exists "^(String.concat " " schDnews)^", " end in
"forall "^(String.concat " " schOb)^", ("^schNameO^" "^(String.concat " " schOs)^") -> ("^exB^schNameD^" "^(String.concat " " schDs)^").\n"


let make_proj_prf i  = 
  let hs = make_n_fresh_hyp  3 "Hinv" in
 (sprintf " %s: induction on 1. intros %s. %s: case %s. \n search. \n" (List.nth hs 0) (List.nth hs 1) (List.nth hs 2) (List.nth hs 1))^(str_repeat i (sprintf "apply %s to %s. search. \n" (List.nth hs 0) (List.nth hs 2)))
 




(* Schema Plugin *)

let process_tactic rPPO st _ =
  let finished = ref false in
  slexbuf := Lexing.from_string st;
    begin try while not !finished do try
      let input = Schemaparser.command Schemalexer.token !slexbuf in
      begin match input with
      | Inversion args ->
(* inv.1 *) 
       begin match (get_hyp (List.hd args), get_hyp (List.hd (List.tl args))) with
       | Pred ( t, r), Pred (t1, _ ) ->
	   let (schName, gi, _) = member_of_ith t t1 in
(* inv.2 *)let hypName = "Hinv"^schName^(string_of_int gi) in
	   begin try
	     let _ = get_hyp hypName in
	     let appStr = "\n apply "^hypName^" to "^(String.concat " " args)^" ." in
	     rPPO appStr
	   with  _ -> 
	     let (arr, bids) = get_schema schName in
(* inv.3 *)  let invThmStr = make_inv_stmt gi schName arr bids  in
	     let invPrfStr = make_inv_prf (List.length bids) in
	     let appStr = "\n apply "^hypName^" to "^(String.concat " " args)^" ." in
	     let aStr = hypName^": assert "^invThmStr^invPrfStr^appStr in
	     try 
	       rPPO  aStr
	     with e -> printf "failed while rec in inv. \n"; raise e
	   end
       | _,_ -> failwith "unexpected in inversion" 
       end
 | Sync args -> 
(* syn.1 *)
   begin match (get_hyp (List.hd args), get_hyp (List.hd (List.tl args))) with
   | Pred ( t, _), Pred (t1, _ ) ->
   let (schName,gi,st) = member_of_ith t t1 in
   let (arr, bids) = get_schema schName in
(* syn.2 *)
   let mts' = List.map (fun (a,b,tml) -> List.nth tml (gi-1)) bids in
   let mts = remove_nones mts' in
   let ads = instOfPats st mts in
(* syn.3 *)
   let adsHashl = List.map (fun (b,_) -> if b then "1" else "0") ads in
   let hypName = "Hsync"^schName^(string_of_int gi)^(String.concat "" adsHashl) in
   begin try
     let _ = get_hyp hypName in
     let appStr = "\n apply "^hypName^" to "^(String.concat " " args)^" ." in
     rPPO appStr

   with  _ -> 
(* syn.4 *)
   let vvts = List.filter (fun (cmts, (b,_)) -> b) (List.combine mts ads) in
   if vvts = [] then failwith (sprintf "Schema: in sync, no clauses of %s can introduce a formula of the form %s. \n" schName (term_to_string st));
   let (tlup,pads) = List.split vvts in
   let hdtlup = List.hd tlup in
   List.iter (fun x -> fail_if_false (Unify.try_left_unify hdtlup x)) (List.tl tlup);
   let ads = instOfPats hdtlup mts in
(* syn.5 *)
   let syncThmStr = make_sync_stmt gi schName arr bids ads hdtlup in
   let syncPrfStr = make_sync_prf ads in 
   let appStr = "\n apply "^hypName^" to "^(String.concat " " args)^" ." in
   let aStr = hypName^" : assert "^syncThmStr^syncPrfStr^appStr in
   rPPO  aStr end
   | _ , _ -> failwith " unexpected in sync" end  
  |  Unique args ->
(* uni.1 *)      let (h0,h1,h2) = ( try (get_hyp (List.nth args 0), 
					 get_hyp (List.nth args 1),
					 get_hyp (List.nth args 2))
with _ -> failwith "Schema: 3 arguments expected for 'unique' tactical" ) in
             begin match (h0,h1,h2) with
	     | Pred(t,_),Pred(t1,_),Pred(t2,_) ->
	 let (schName , gi ,te1) = (member_of_ith t t1) in
	 let (schName', gi',te2) = (member_of_ith t t2) in
	 (if  (gi <> gi' || schName <> schName') then failwith "Schema: membership hypothesis should come from the same projection of the context in 'unique' tactical");
		  let (arr,bids) = get_schema schName in
		  let mts' = List.map (fun (a,b,tml) -> (List.nth tml (gi-1))) bids  in
		  let mts  = remove_nones mts' in
(* uni.2 *)       let varl = pairwiseEqual te1 te2 in

(* uni.3 *)       fail_if_false (Unify.try_left_unify te1 te2);

(* uni.4 *)       let ads = instOfPats te1 mts in
(* uni.5 *)       let (groundVar, rel) = safeUniqueGrounds mts ads varl in
(* uni.6 *)       let adsHashl = List.map (fun (b,_) -> if b then "1" else "0") ads in
                  let hypName = "Huni"^schName^(string_of_int gi)^(List.hd rel)^(String.concat "" adsHashl) in
         	  begin try
                     let _ = get_hyp hypName in
	     let appStr = "\n apply "^hypName^" to "^(String.concat " " args)^" ." in
	     rPPO appStr

                  with  _ -> 
(* uni.7 *)       let vvts = List.filter (fun (cmts, (b,_)) -> b) (List.combine mts ads) in
                  let (pmts,pads) = List.split vvts in


		  let tlup = List.map (fun (tm,oldid) -> 
		     let gvSwap = ((groundVar,oldid)::[(oldid,groundVar)]) in
		     (rename_ids_in_term gvSwap tm)) (List.combine pmts rel) in
		  let hdtlup = List.hd tlup in
		  List.iter (fun x -> fail_if_false (Unify.try_left_unify hdtlup x)) (List.tl tlup);
(* uni.8 *)       let (nl,tu1,tu2) = uniteTerms hdtlup groundVar in
		  let (bads,_) = List.split ads in
		  let uniThmStr = make_uni_stmt schName tu1 tu2 nl arr gi groundVar in
                  let uniPrfStr = make_uni_prf schName mts bads in
		  let appStr = "\n apply "^hypName^" to "^(String.concat " " args)^" ." in
		  let aStr = hypName^" : assert "^uniThmStr^uniPrfStr^appStr in
		  rPPO aStr end
	     | _ -> failwith "Schema: arguments in the wrong form for 'unique' tactical"
	     end  
  |  Projection (argsd,args) -> 
(* pro.1 *)  
(*        ((if List.length hl < 3 then failwith "Schema: Not enough argument for projas"); *)
	let schNameD = List.hd (argsd) in
	let schDs = List.tl (argsd) in
	(begin match (get_hyp (List.hd args)) with 
	| Pred (t,_) -> 
	    (begin match observe t with
	    | App(schNameT,schGsTl) ->
	       let schNameO = term_to_string schNameT in
	       let schOs = List.map get_head_id schGsTl in
	       (if (List.mem_assoc schNameO Prover.(!schemas)) then
		 if (List.mem_assoc schNameD Prover.(!schemas)) then
		   ()
		 else failwith ("Schema: "^schNameD^" is not a declared schema.")
	       else failwith ("Schema: "^schNameO^" is not a declared schema."));
	       let (arrD,bidsD) = get_schema schNameD in
	       let (arrO,bidsO) = get_schema schNameO in
	       (if (List.length schOs) = arrO then 
		 if (List.length schDs) = arrD then 
		   ()
		 else failwith (sprintf "Schema: %d arguments expected for schema %s." arrD schNameD)
	       else failwith (sprintf "Schema: %d arguments expected for schema %s." arrO schNameO));
(* pro.2 *)    let odPerm = List.map (fun id -> 
                                    try 
				      string_of_int (mem_pos id schDs)
				    with _ -> "0") schOs in
	       let hypName = "Hpro"^schNameO^(String.concat "" odPerm)^schNameD in
	       begin try 
		 let _ = get_hyp hypName in
		 let appStr = "\n apply "^hypName^" to "^(String.concat " " args)^" ." in
		 rPPO appStr
	       with _ ->
(* pro.3 *)    let (_,_,btmsO) = split3 bidsO in
	       let clConsO = proClConst schOs btmsO in
	       if (List.flatten clConsO) = [] then failwith "Schema: Couldn't create the constraints from the original schema in projection tactic";
               let (_,_,btmsD) = split3 bidsD in
                checkProMatches clConsO schDs btmsD;   
(* pro.4 *)    let projThmStr =  make_proj_stmt schNameO schOs schNameD schDs in
	       let projPrfStr =  make_proj_prf (List.length bidsO) in
	       let appStr = "\n apply "^hypName^" to "^(String.concat " " args)^" ." in
	       let aStr =  hypName^" : assert "^projThmStr^projPrfStr^appStr in
	       rPPO aStr
	       end
	    | _ -> failwith "Schema: Unexpected in projas (1)" 
	    end)
	| _ -> failwith "Schema: Unexpected in projas (2)"
	end) end
    with 
    | End_of_file -> failwith "eof"
    | Parsing.Parse_error ->
        eprintf "Failure to apply Ctx tactic. \n Syntax error in Schema plugin (process_tactic) %s.\n%!" st;
        Lexing.flush_input !slexbuf;
	flush stderr;
	failwith "eof"
    | e -> (eprintf "Failure to apply Ctx tactic. \n Error %s while processing command %s in Schema plugin. \n" (Printexc.to_string e) st); Lexing.flush_input !slexbuf; flush stderr; failwith "eof"
    done with
      | Failure "eof" -> ()
    end



let process_top rPO st = 
  let finished = ref false in
  slexbuf := Lexing.from_string st;
    begin try while not !finished do try
      let input = Schemaparser.top_command Schemalexer.token !slexbuf in
      begin match input with
      | SchemaDef (id,cll) -> 
           (* check that the name of the schema wasn't previous used *)
            check_noredef [id];
	    if cll = [] then failwith "Can't declare an empty schema";
            (*verify that the arity is the same for every clause (save the result), *)
		let arr = (fun (_,_,cl) -> List.length cl) (List.hd cll) in
		List.iter (fun (_,_,cl) -> if arr = (List.length cl) then () else failwith (sprintf "All clauses of %s should have the same arity (%d)" id arr)) cll;
	    (* in each clause, type each of the blocks *)
		let clgenl = List.map (fun (eb,nb,cl) -> 
		  let eb = List.unique eb in
		  List.iter (fun id -> if not (id.[0] = Char.uppercase (id.[0])) then failwith ("Exists bound variables must start with an uppercase character, in declaration of "^id)) eb;
		  let nb = List.unique nb in
		  let (ebidtys,nbidtys) = List.fold_left (fun (ebit,nbit) out ->
		      begin match out with 
		      |	None ->  (ebit,nbit)
		      |	Some ut ->
			  let vlist = type_vars_in (uterm_to_term [] ut) (Ty( [], "o")) sign in
			  let (ebit',nbit') = List.partition (fun (id,ty) -> List.mem id eb) vlist in
			  List.iter (fun (id,ty) -> if not (List.mem id nb) then failwith ("Schema: Unknown constant "^id^"\n")) nbit';
			  (append_uni_assocs ebit ebit', append_uni_assocs nbit nbit')
		      end) ([],[]) cl in
		  let (_,tys1) = List.split ebidtys in
		  let (_,tys2) = List.split nbidtys in
		  let genStr = makeBlockGeneric tys1 tys2 in
		  let ebctx = tyctx_to_logical_ctx ebidtys in
		  let nbctx = tyctx_to_nominal_ctx nbidtys in
		  let tyctx = List.append ebctx nbctx in
		  let clt = List.map (fun out -> begin match out with
		  | None -> None
		  | Some ut -> Some (type_uterm ~sr:!sr ~sign:!sign ~ctx:tyctx ut) end) cl in
		  ((ebidtys,nbidtys,clt),genStr)) cll in
		let (cll',genl) = List.split clgenl in
		let cll'' = List.filter (fun (eb,nb,clt) ->  not (all_none clt)) cll' in (* remove empty clauses *)
		if cll'' = [] then failwith "Schema: Trying to define an empty schema. \n";
		let genStr = String.concat " \n" genl in
		add_schema id (arr, cll'');
		saveSchema := Some id;
		let cdef = make_schema_def id arr cll'' in
		rPO  (cdef^" \n "^genStr);
      end
    with 
    | End_of_file -> failwith "eof"
    | Parsing.Parse_error ->
        eprintf "Syntax error in Schema plugin (process_top) %s.\n%!" st;
	flush stderr;
        Lexing.flush_input !slexbuf ;
	try_del_schema ();
	failwith "eof"
    | e -> (eprintf "Error %s while processing top command %s in Schema plugin. \n" (Printexc.to_string e) st); flush stderr; Lexing.flush_input !slexbuf ; try_del_schema (); failwith "eof"
    done with
      | Failure "eof" -> ()
    end
