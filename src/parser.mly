/****************************************************************************
 * Bedwyr prover                                                            *
 * Copyright (C) 2006 David Baelde, Alwen Tiu, Axelle Ziegler               *
 *                                                                          *
 * This program is free software; you can redistribute it and/or modify     *
 * it under the terms of the GNU General Public License as published by     *
 * the Free Software Foundation; either version 2 of the License, or        *
 * (at your option) any later version.                                      *
 *                                                                          *
 * This program is distributed in the hope that it will be useful,          *
 * but WITHOUT ANY WARRANTY; without even the implied warranty of           *
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *
 * GNU General Public License for more details.                             *
 *                                                                          *
 * You should have received a copy of the GNU General Public License        *
 * along with this code; if not, write to the Free Software Foundation,     *
 * Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *
 ****************************************************************************/

%{
  let eq   = Term.binop System.Logic.eq
  let andc = Term.binop System.Logic.andc
  let orc  = Term.binop System.Logic.orc
  let imp  = Term.binop System.Logic.imp

  let to_string t =
    match Term.observe t with
      | Term.Var {Term.name=s;Term.tag=Term.Constant} -> s
      | _ -> assert false

  let mkdef kind head params body =
    (* Replace the params by fresh variables and
     * put the constraints on the parameters in the body:
     * d (s X) X := body --> d Y X := (Y = s X), body
     * As an input we get: [head] (d) [params] ([s X;X]) and [body]. *)

    (* Create the prolog (new equalities added to the body) and the new set
     * of variables used as parameters.
     * A parameter can be left untouched if it's a variable which didn't
     * occur yet. *)
    let new_params,prolog =
      List.fold_left
        (fun (new_params,prolog) p ->
           match Term.observe p with
             | Term.Var {Term.tag=Term.Logic}
                 when List.for_all (fun v -> v!=p) new_params ->
                 p::new_params,prolog
             | _  ->
                 let v = Term.fresh 0 in
                   (v::new_params, (eq v p)::prolog))
        ([],[])
        params
    in
    (* Add prolog to the body *)
    let body = if prolog = [] then body else
      Term.app (Term.atom System.Logic.andc) (prolog@[body])
    in
    (* Quantify existentially over the initial free variables. *)
    let body =
      List.fold_left
        (fun body v ->
           if List.mem v new_params then body else
             Term.app (Term.atom System.Logic.exists)
               [Term.abstract_var v body])
        body
        (Term.logic_vars (body::params))
    in
    (* Finally, abstract over parameters *)
    let arity,body =
      if new_params = [] then 0,body else
        let body =
          List.fold_left (fun body v -> Term.abstract_var v body)
            body
            new_params
        in match Term.observe body with
          | Term.Lam (n,b) -> n,b
          | _ -> assert false
    in
      System.Def (kind, to_string head, arity, body)

%}

%token BSLASH LPAREN RPAREN DOT SHARP
%token EQ AND IMP RARROW LARROW OR PLUS MINUS TIMES
%token DEF IND COIND
%token <string> ID
%token <string> STRING

%nonassoc BSLASH
%right IMP
%left AND
%left OR
%nonassoc EQ
%right RARROW
%left LARROW
%left PLUS
%left MINUS
%left TIMES

%start input_def input_query
%type <System.input> input_def
%type <System.input> input_query

%%

input_def:
| defkind sexp DEF exp DOT { let h,t = $2 in mkdef $1 h t $4 }
| defkind sexp DOT         { let h,t = $2 in mkdef $1 h t (Term.atom "true") }
| DEF exp DOT              { System.Query $2 }
| SHARP sexp DOT           { let h,t = $2 in System.Command (to_string h,t) }
defkind:
|       { System.Normal      }
| IND   { System.Inductive   }
| COIND { System.CoInductive }

input_query:
| exp DOT          { System.Query $1 }
| SHARP sexp DOT   { let (h,t) = $2 in System.Command (to_string h,t) }

exp:
| exp EQ   exp { eq   $1 $3 }
| exp AND  exp { andc $1 $3 }
| exp OR   exp { orc  $1 $3 }
| exp IMP  exp { imp  $1 $3 }
| iexp         { $1 }
| sexp         { let (t,l) = $1 in Term.app t l }

sexp:
| lexp { match $1 with
          | [] -> assert false
          | t::l -> t,l }
lexp:
| aexp          { [$1] }
| ID BSLASH exp { [Term.abstract $1 $3] }
| aexp lexp     { $1::$2 }

aexp:
| LPAREN exp RPAREN { $2 }
| ID { Term.atom $1 }
| STRING { Term.string $1 }

/* There is redundency here, but ocamlyacc seems to have problems
   with left associativity if we abstract it. */
iexp:
| exp LARROW exp { Term.app (Term.atom "<-") [$1; $3] }
| exp RARROW exp { Term.app (Term.atom "->") [$1; $3] }
| exp PLUS   exp { Term.app (Term.atom "+")  [$1; $3] }
| exp MINUS  exp { Term.app (Term.atom "-")  [$1; $3] }
| exp TIMES  exp { Term.app (Term.atom "*")  [$1; $3] }

%%

(** Parse a .def file and return the abstract syntax tree as a term.
  * It doesn't have position information, and abstractions make some names
  * disappear, but this could be changed later.
  * [term_of_file] will recurse through #includes and inline them. *)
let to_term lexer file =
  let lam  = Term.const "lam" 0  in
  let app  = Term.const "app" 0  in
  let atom = Term.const "atom" 0 in
  let binder x = match Term.observe x with
    | Term.Var {Term.name="sigma"}
    | Term.Var {Term.name="pi"}
    | Term.Var {Term.name="nabla"} -> true
    | _ -> false
  in
  let logic x = match Term.observe x with
    | Term.Var {Term.name="="}
    | Term.Var {Term.name="=>"}
    | Term.Var {Term.name=","}
    | Term.Var {Term.name=";"} -> true
    | _ -> false
  in
  let rec split acc = function
    | [] -> assert false
    | [x] -> x,List.rev acc
    | x::tl -> split (x::acc) tl
  in
  (* De-flatten conjunction, disjunctions and application,
   * add explicit abstractions, applications and atom constructors. *)
  let rec objectify term =
    match Term.observe term with
      | Term.Lam (0,x) -> objectify x
      | Term.Lam (n,x) ->
          Term.app lam [Term.lambda 1 (objectify (Term.lambda (n-1) x))]
      | Term.App (x,h::tl) ->
          if binder x then begin
            assert (tl = []) ;
            match Term.observe h with
              | Term.Lam (1,h) -> Term.app x [Term.lambda 1 (objectify h)]
              | _ -> assert false
          end else if logic x then
            if tl=[] then objectify h else
              Term.app x [ objectify h ;
                           objectify (Term.app x tl) ]
          else
            if tl=[] then Term.app app [ objectify x; objectify h ] else
              let y,l = split [] (h::tl) in
                Term.app app [ objectify (Term.app x l);
                               objectify y ]
      | _ -> Term.app atom [term]
  in
  let clause  = Term.const "clause"  0 in
  let query   = Term.const "query"   0 in
  let command = Term.const "command" 0 in
  let rec list_of_file file list =
    let lexbuf = Lexing.from_channel (open_in file) in
    let rec aux l =
      let input =
        try
          Some (input_def lexer lexbuf)
        with Failure "eof" -> None
      in
        match input with
          | None -> l
          | Some i ->
              begin match i with
                | System.Def (_,head,arity,body) ->
                    let body = objectify (Term.lambda arity body) in
                      aux ((Term.app clause [ Term.const head 0;
                                              body ])::l)
                | System.Query a -> aux ((Term.app query [a])::l)
                | System.Command ("include",[file]) ->
                    begin match Term.observe file with
                      | Term.Var {Term.name=file} ->
                          let cwd = Sys.getcwd () in
                            Sys.chdir (Filename.dirname file) ;
                            let l = list_of_file file l in
                              Sys.chdir cwd ;
                              aux (list_of_file file l)
                      | _ -> assert false
                    end
                | System.Command ("assert",a) ->
                    aux ((Term.app command ((Term.const "assert" 0)::
                                              (List.map objectify a)))::l)
                | System.Command (c,a) ->
                    aux ((Term.app command ((Term.const c 0)::a))::l)
              end
    in
    let cwd = Sys.getcwd () in
      Sys.chdir (Filename.dirname file) ;
      let l = aux [] in
        Sys.chdir cwd ;
        l
  in
  let cons = Term.binop "cons" in
  let rec term_of_list t = function
    | [] -> t
    | hd::tl -> term_of_list (cons hd t) tl
  in
    term_of_list (Term.const "nil" 0) (list_of_file file [])
