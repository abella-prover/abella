/****************************************************************************/
/* Copyright (C) 2007-2009 Gacek                                            */
/* Copyright (C) 2013-2022 Inria (Institut National de Recherche            */
/*                         en Informatique et en Automatique)               */
/*                                                                          */
/* This file is part of Abella.                                             */
/*                                                                          */
/* Abella is free software: you can redistribute it and/or modify           */
/* it under the terms of the GNU General Public License as published by     */
/* the Free Software Foundation, either version 3 of the License, or        */
/* (at your option) any later version.                                      */
/*                                                                          */
/* Abella is distributed in the hope that it will be useful,                */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of           */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            */
/* GNU General Public License for more details.                             */
/*                                                                          */
/* You should have received a copy of the GNU General Public License        */
/* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          */
/****************************************************************************/

%{

  open Extensions
  open Typing

  open struct module Types = Abella_types end

  let error_report ?(pos=Parsing.symbol_start_pos ()) fmt =
    let open Lexing in
    let parse_fmt = "@.%s:@\nError: @[" ^^ fmt ^^ "@]@." in
    let pos_string =
      if pos == Lexing.dummy_pos then
        "Unknown position"
      else
        Printf.sprintf "File %S, line %d, character %d"
          pos.pos_fname pos.pos_lnum
          (pos.pos_cnum - pos.pos_bol + 1)
    in
    Output.msg_formatk
      (fun _ -> raise Types.Reported_parse_error)
      ~severity:Error parse_fmt pos_string

  let predefined ~pos id =
    UCon(pos, id, Term.fresh_tyvar ())

  let binop ~pos id t1 t2 =
    UApp(pos, UApp(pos, predefined ~pos id, t1), t2)

  let nested_app head args =
    List.fold_left
      (fun h a -> UApp((fst (get_pos h), snd (get_pos a)), h, a))
      head args

  let rec iterated_app n f x =
    if n <= 0 then x else
      let bod = iterated_app (n - 1) f x in
      UApp((fst (get_pos f), snd (get_pos bod)), f, bod)

  let is_illegal_constant k = Term.is_nominal_name k

  let binding_cons (x, ty) tids =
    if List.mem_assoc x tids then
      error_report "Repeated bound variable %s" x
    else
      (x, ty) :: tids

  let check_legal_var vid pos =
    if is_illegal_constant vid then
      error_report ~pos
        "Invalid bound variable %S.@\nIdentifiers matching n[0-9]+ are reserved for nominal constants." vid

  let deloc_id { el = id ; pos = (pos, _) } =
    if is_illegal_constant id then
      error_report ~pos
        "Invalid bound variable %S.@\n\
         Identifiers matching n[0-9]+ are reserved for nominal constants."
        id ;
    id

  let deloc_id_ty (lid, ty) = (deloc_id lid, ty)

  let make_sig (sigid : string wpos) (sigpre : string wpos list) sigdecls =
    let badconsts = ref [] in
    let collect_bad_decl decl =
      match decl.el with
      | Abella_types.SKind _ -> ()
      | Abella_types.SType (ids, _) ->
         List.iter begin fun k ->
           if is_illegal_constant k.el then
             badconsts := k.el :: !badconsts
           end ids
    in
    List.iter collect_bad_decl sigdecls ;
    match List.rev !badconsts with
    | [] -> Abella_types.Sig { name = sigid ;
                               accum_sig = sigpre ;
                               decls = sigdecls }
    | (_k :: _) as ks ->
      let ks = String.concat ", " ks in
      error_report "Invalid signature constants: %s@\n\
                    Identifiers matching n[0-9]+ are reserved for nominal constants." ks

  let id_to_aty id =
    if Term.is_capital_name id then
      Term.Tygenvar id
    else
      Term.atybase id

  let cmdline_arg_one a =
    match String.split_on_char '=' a with
    | [a ; b] -> begin
        match int_of_string_opt b with
        | Some n -> (a, Abella_types.Int n)
        | None -> (a, Abella_types.Str b)
      end
    | _ -> raise Abella_types.Reported_parse_error

  let cmdline_arg_two a b =
    match String.split_on_char '=' a with
    | [a ; ""] -> (a, b)
    | _ -> raise Abella_types.Reported_parse_error

%}

%token IMP IF AMP COMMA DOT BSLASH LPAREN RPAREN TURN CONS EQ TRUE FALSE DEFEQ
%token IND INST APPLY CASE FROM SEARCH TO ON WITH INTROS CUT ASSERT CLAUSEEQ
%token SKIP UNDO ABORT COIND LEFT RIGHT MONOTONE IMPORT BY
%token SPLIT SPLITSTAR UNFOLD ALL KEEP CLEAR SPECIFICATION SEMICOLON
%token THEOREM DEFINE PLUS CODEFINE SET ABBREV UNABBREV QUERY SHOW SUSPEND
%token PERMUTE BACKCHAIN COMPUTE QUIT UNDERSCORE AS SSPLIT RENAME
%token BACK RESET
%token COLON RARROW FORALL NABLA EXISTS WITNESS STAR AT HASH OR AND CARET
%token LBRACE RBRACE LBRACK RBRACK
%token KIND TYPE KKIND TTYPE SIG MODULE ACCUMSIG ACCUM END CLOSE

%token <int> NUM
%token <string> STRINGID QSTRING CLAUSENAME
%token EOF

/* Lower */

%nonassoc COMMA
%right RARROW
%left OR
%left AND

%nonassoc BSLASH
%left IF
%right IMP
%left AMP

%right CONS

/* Higher */


%start lpmod lpsig
%start top_command_start command_start any_command_start
%start sig_decl mod_clause search_witness depth_spec
%start one_term one_metaterm one_defs one_sig_body one_mod_body
%start cmdline_flags

%type <Typing.uterm> term
%type <Typing.umetaterm> metaterm
%type <Abella_types.lpsig> lpsig
%type <Abella_types.lpmod> lpmod
%type <Abella_types.sig_decl> sig_decl
%type <Abella_types.uclause Extensions.wpos> mod_clause
%type <Abella_types.udef_clause list> defs
%type <Abella_types.command Extensions.wpos> command_start
%type <Abella_types.top_command Extensions.wpos> top_command_start
%type <Abella_types.any_command Extensions.wpos> any_command_start
%type <Abella_types.witness> search_witness
%type <(int * int option) list> depth_spec

%type <Typing.uterm> one_term
%type <Typing.umetaterm> one_metaterm
%type <Abella_types.sig_decl list> one_sig_body
%type <Abella_types.uclause Extensions.wpos list> one_mod_body
%type <Abella_types.udef_clause list> one_defs
%type <(string * Abella_types.set_value) list> cmdline_flags

%%

any_command_start: com=located(any_command) { com }
command_start: com=located(command) { com }
top_command_start: com=located(top_command) { com }

hyp:
  | x=STRINGID
    { check_legal_var x $startpos ; x }
  | UNDERSCORE
    { "_" }

loc_id:
  | x=located(id)
    { x }

id:
  | x=STRINGID    { x }
  | ABBREV        { "abbrev" }
  | ABORT         { "abort" }
  | ALL           { "all" }
  | APPLY         { "apply" }
  | AS            { "as" }
  | ASSERT        { "assert" }
  | BACKCHAIN     { "backchain" }
  | CASE          { "case" }
  | CLEAR         { "clear" }
  | COIND         { "coinduction" }
  | COMPUTE       { "compute" }
  | CUT           { "cut" }
  | FROM          { "from" }
  | IND           { "induction" }
  | INST          { "inst" }
  | INTROS        { "intros" }
  | KEEP          { "keep" }
  | KKIND         { "Kind" }
  | LEFT          { "left" }
  | MONOTONE      { "monotone" }
  | ON            { "on" }
  | PERMUTE       { "permute" }
  | RENAME        { "rename" }
  | RIGHT         { "right" }
  | SEARCH        { "search" }
  | SKIP          { "skip" }
  | SPLIT         { "split" }
  | TO            { "to" }
  | UNABBREV      { "unabbrev" }
  | UNDO          { "undo" }
  | UNFOLD        { "unfold" }
  | WITH          { "with" }
  | WITNESS       { "witness" }

/* Kind */
knd:
  | TYPE
    {Term.kind 0}
  | TYPE; RARROW; k=knd
    {Term.kincr k}

/* Annotated ID */
aid:
  | x=loc_id
    { (x, Term.fresh_tyvar ()) }
  | x=loc_id; COLON; ty=ty
    { (x, ty) }

/* Parenthesized annotated ID */
paid:
  | x=loc_id
    { (x, Term.fresh_tyvar ()) }
  | LPAREN; x=loc_id; COLON; ty=ty; RPAREN
    { (x, ty) }
  | UNDERSCORE
    { ({ el = "_" ; pos = $loc($1) }, Term.fresh_tyvar ()) }
  | LPAREN; UNDERSCORE; COLON; ty=ty; RPAREN
    { ({ el = "_" ; pos = $loc($2) }, ty) }

contexted_term:
  | cx=context; TURN; gl=term
    { (cx, gl) }
  | gl=term
    { (predefined ~pos:$loc "nil", gl) }

focused_term:
  | cx=context; COMMA; LBRACK; foc=term; RBRACK; TURN; goal=term
    { (cx, foc, goal) }
  | LBRACK; foc=term; RBRACK; TURN; goal=term
    { (predefined ~pos:$loc "nil", foc, goal) }

context:
  | cx=context; COMMA; f=term
    { binop ~pos:$loc "::" f cx }
  | f=term
    { if has_capital_head f then f
      else binop ~pos:$loc "::" f (predefined ~pos:$loc "nil") }

term:
  | f=term; IMP; g=term
    { binop ~pos:$loc($2) "=>" f g }
  | g=term; IF; f=term
    { binop ~pos:$loc($2) "=>" f g }
  | f=term; AMP; g=term
    { binop ~pos:$loc($2) "&" f g }
  | x=term; CONS; l=term
    { binop ~pos:$loc($2) "::" x l }
  | v=aid; BSLASH; bod=term
    { let (id, ty) = v in
      let id = deloc_id id in
      ULam($loc(v), id, ty, bod) }
  | e=exp; es=exp_list
    { nested_app e es }
  | f=exp; CARET; n=NUM; x=exp
    { iterated_app n f x }
  | e=exp
    { e }

exp:
  | LPAREN; t=term; RPAREN
    { change_pos $loc t }
  | vty=paid
    { let (id, ty) = vty in
      UCon($loc, id.el, ty) }

exp_list:
  | e=exp; es=exp_list
    { e :: es }
  | e=exp
    { [e] }
  | vty=aid; BSLASH; bod=term
    { let (id, ty) = vty in
      let id = deloc_id id in
      [ULam($loc, id, ty, bod)] }

lpsig:
  | SIG; head=loc_id; DOT;
    pre=flatten(list(ACCUMSIG; ms=id_list; DOT {ms}));
    body=list(located(sig_decl)); lpend
    { make_sig head pre body }

sig_decl:
  | KIND; tys=id_list; ki=located(knd); DOT
    { Types.SKind(tys, ki) }
  | TYPE; cs=id_list; ty=located(ty); DOT
    { Types.SType(cs, ty) }

lpmod:
  | MODULE; head=loc_id; DOT;
    pre=flatten(list(ACCUM; ms=id_list; DOT {ms}));
    cls=list(mod_clause); lpend
    { Types.Mod { name = head ;
                  accum = pre ;
                  clauses = cls } }

mod_clause:
  | cn=clause_name; cl=located(clause)
    { let (h, b) = cl.el in { el = (cn, h, b) ; pos = cl.pos } }

%inline lpend:
  | END | EOF { }

%inline
id_list:
   | xs=separated_nonempty_list(COMMA, loc_id)
     { xs }

pty:
  | a=id
    { Term.tybase (id_to_aty a) }
  | LPAREN; a=ty; RPAREN
    {a}

aty:
  | a=id
    { id_to_aty a }
  | a=aty; b=pty
    {
      let open Term in
      match a with
      | Tycons _ -> atyapp a b
      | Tygenvar _ ->
         error_report ~pos:$startpos
           "Type variable cannot be applied to arguments"
      | _ -> assert false
    }

ty:
  | a=aty
    { Typing.desugar_ty (Term.tybase a) }
  | a=ty; RARROW; b=ty
    { Term.tyarrow [a] b }
  | LPAREN; a=ty; RPAREN
    { a }

clause_name:
  | cn=CLAUSENAME
    { check_legal_var cn $startpos ;
      Some cn }
  |
    { None }

clause:
  | head=clause_head; DOT
    { (head, []) }
  | head=clause_head; CLAUSEEQ; body=clause_body; DOT
    { (head, body) }
  | head=clause_head; IF; body=clause_body; DOT
    { (head, body) }

clause_head:
  | LPAREN; head=clause_head; RPAREN
    { head }
  | f=paid; args=loption(exp_list)
    { let (id, ty) = f in
      nested_app (UCon($loc(f), id.el, ty)) args }

clause_body:
  | t=term; COMMA; bod=clause_body
    { t :: bod }
  | LPAREN; t=term; COMMA; bod=clause_body; RPAREN
    { t :: bod }
  | t=term
    { [t] }

defs:
  | ds=separated_nonempty_list(SEMICOLON, def)
    { ds }

def:
  | head=metaterm;
    { (head, UTrue) }
  | head=metaterm; DEFEQ; body=metaterm
    { (head, body) }

%inline
perm:
  | LPAREN; vs=nonempty_list(id); RPAREN
    { vs }

any_command:
  | cmd=pure_top_command
    { Types.ATopCommand(cmd) }
  | cmd=pure_command
    { Types.ACommand(cmd) }
  | cmd=common_command
    { Types.ACommon(cmd) }

command:
  | cmd=pure_command
    { cmd }
  | cmd=common_command
    { Types.Common(cmd) }

clearable:
  | clr=boption(STAR); h=hyp; ins=maybe_inst
    { if clr then Types.Remove(h, ins) else Types.Keep(h, ins) }

%inline
maybe_inst:
  | vs=loption(LBRACK; vs=separated_nonempty_list(COMMA, uty); RBRACK {vs})
    { vs }

uty:
  | a=ty
    { a }
  | UNDERSCORE
    { Term.fresh_tyvar () }

%inline
aty_list:
  | tys=separated_nonempty_list(COMMA, aty)
    { List.map Typing.desugar_aty tys }

%inline
apply_args:
  | ts=nonempty_list(apply_arg)
    { ts }

apply_arg:
  | h=hyp; ins=maybe_inst
    { Types.Keep (h, ins) }
  | STAR; h=STRINGID; ins=maybe_inst
    { check_legal_var h $startpos(h) ;
      Types.Remove (h, ins) }

maybe_depth:
  | n=option(NUM) { n }

pure_command:
  | ht=hhint; IND; ON; ns=num_list; DOT
    { Types.Induction(ns, ht) }
  | ht=hhint; COIND; DOT
    { Types.CoInduction(ht) }
  | ht=hhint; APPLY; dep=maybe_depth; clr=clearable;
    args=loption(TO; args=apply_args {args});
    ws=loption(WITH; ws=withs {ws}); DOT
    { Types.Apply(dep, clr, args, ws, ht) }
  | ht=hhint; COMPUTE; dp=option(NUM); hs=nonempty_list(clearable); DOT
    { Types.Compute (hs, dp, ht) }
  | BACKCHAIN; dep=maybe_depth; clr=clearable;
    ws=loption(WITH; ws=withs {ws}); DOT
    { Types.Backchain(dep, clr, ws) }
  | ht=hhint; CUT; LPAREN; f=term; RPAREN; FROM;
    fa=clearable; WITH; fb=clearable; DOT
    { Types.CutFrom(fa, fb, f, ht) }
  | ht=hhint; CUT; fa=clearable; WITH; fb=clearable; DOT
    { Types.Cut(fa, fb, ht) }
  | ht=hhint; CUT; f=clearable; DOT
    { Types.SearchCut(f, ht) }
  | ht=hhint; INST; clr=clearable; WITH; ws=withs; DOT
    { Types.Inst(clr, ws, ht) }
  | ht=hhint; CASE; h=hyp;
    kp=boption(LPAREN; KEEP; RPAREN {()}); DOT
    { let ca = if kp then Types.Keep(h, []) else Types.Remove(h, []) in
      Types.Case(ca, ht) }
  | ht=hhint; ASSERT; dep=maybe_depth; f=metaterm; DOT
    { Types.Assert(f, dep, ht) }
  | ht=hhint; MONOTONE; clr=clearable; WITH; t=term; DOT
    { Types.Monotone(clr, t, ht) }
  | EXISTS; ew=ewitnesses; DOT
    { Types.Exists(`EXISTS, ew) }
  | WITNESS; ew=ewitnesses; DOT
    { Types.Exists(`WITNESS, ew) }
  | SEARCH; DOT
    { Types.Search(`nobounds) }
  | SEARCH; dep=NUM; DOT
    { Types.Search(`depth dep) }
  | SEARCH; WITH; wit=search_witness; DOT
    { Types.Search(`witness wit) }
  | SPLIT; DOT
    { Types.Split }
  | SPLITSTAR; DOT
    { Types.SplitStar }
  | LEFT; DOT
    { Types.Left }
  | RIGHT; DOT
    { Types.Right }
  | INTROS; hs=loption(hyp_list); DOT
    { Types.Intros hs }
  | SKIP; DOT
    { Types.Skip }
  | ABORT; DOT
    { Types.Abort }
  | UNDO; DOT
    { Types.Undo }
  | UNFOLD; csel=clause_sel; ssel=sol_sel; DOT
    { Types.Unfold (csel, ssel) }
  | CLEAR; hs=hyp_list; DOT
    { Types.Clear(Types.Clear_delete, hs) }
  | CLEAR; RARROW; hs=hyp_list; DOT
    { Types.Clear(Types.Clear_extro, hs) }
  | ABBREV; hs=hyp_list; ab=QSTRING; DOT
    { Types.Abbrev(hs, ab) }
  | UNABBREV; hs=hyp_list; DOT
    { Types.Unabbrev(hs) }
  | RENAME; f=STRINGID; TO; t=STRINGID; DOT
    { check_legal_var f $startpos(f) ;
      check_legal_var t $startpos(t) ;
      Types.Rename(f, t) }
  | PERMUTE; p=perm; h=option(hyp); DOT
    { Types.Permute(p, h) }

%inline
hhint:
  | x=STRINGID; COLON
    { check_legal_var x $startpos(x) ; Some x }
  |
    { None }

%inline
hyp_list:
  | hs=nonempty_list(hyp) { hs }

%inline
num_list:
  | ns=nonempty_list(NUM) { ns }

%inline
ewitnesses:
  | ews=separated_nonempty_list(COMMA, ewitness) { ews }

ewitness:
  | x=id; EQ; t=term
    { Types.ESub (x, t) }
  | t=term
    { Types.ETerm t }

%inline
withs:
  | ws=separated_nonempty_list(COMMA, x=id; EQ; t=term {(x, t)})
    { ws }

clause_sel:
  | { Types.Select_any }
  | n=NUM
    { Types.Select_num n }
  | x=STRINGID
    { check_legal_var x $startpos ;
      Types.Select_named x }

sol_sel:
  | { Types.Solution_first }
  | LPAREN ALL RPAREN
    { Types.Solution_all }

metaterm:
  | TRUE
    { UTrue }
  | FALSE
    { UFalse }
  | t1=term; EQ; t2=term
    { UEq(t1, t2) }
  | q=binder; vs=binding_list; COMMA; bod=metaterm
    { UBinding(q, vs, bod) }
  | f=metaterm; RARROW; g=metaterm
    { UArrow(f, g) }
  | f=metaterm; OR; g=metaterm
    { UOr(f, g) }
  | f=metaterm; AND; g=metaterm
    { UAnd(f, g) }
  | LPAREN; f=metaterm; RPAREN
    { f }
  | f=objseq
    { f }
  | p=term; res=restriction
    { UPred(p, res) }

objseq:
  | LBRACE; cxg=contexted_term; RBRACE; res=restriction
    { let l, g = cxg in
      UAsyncObj(l, g, res) }
  | LBRACE; cxg=focused_term; RBRACE; res=restriction
    { let l, f, g = cxg in
      USyncObj(l, f, g, res) }

binder:
  | FORALL
    { Metaterm.Forall }
  | EXISTS
    { Metaterm.Exists }
  | NABLA
    { Metaterm.Nabla }

binding_list:
  | bs=flatten(nonempty_list(binding_one))
    { bs }

binding_one:
  | id
    { [$1, Term.fresh_tyvar ()] }
  | LPAREN; vs=binding_vars; COLON; ty=ty; RPAREN
    { List.fold_right (fun x tids -> binding_cons (x, ty) tids) vs [] }

binding_vars:
  | bs=nonempty_list(id)
    { bs }

restriction:
  | { Metaterm.Irrelevant }
  | rs=nonempty_list(STAR {()})
    { Metaterm.Smaller (List.length rs) }
  | rs=nonempty_list(AT {()})
    { Metaterm.Equal (List.length rs) }
  | rs=nonempty_list(PLUS {()})
    { Metaterm.CoSmaller (List.length rs) }
  | rs=nonempty_list(HASH {()})
    { Metaterm.CoEqual (List.length rs) }

id_tys:
  | xts=separated_nonempty_list(COMMA, x=loc_id; COLON; ty=ty {deloc_id_ty (x, ty)})
    { xts }

top_command:
  | com=pure_top_command
    { com }
  | com=common_command
    { Types.TopCommon(com) }

theorem_typarams:
  | { [ ] }
  | LBRACK; vs=id_list; RBRACK
    { List.map deloc_id vs }

pure_top_command:
  | THEOREM; x=loc_id; thm=theorem_typarams; COLON; bod=metaterm; DOT
    { Types.Theorem(deloc_id x, thm, bod) }
  | DEFINE; xs=id_tys; BY; option(SEMICOLON); ds=defs; DOT
    { Types.Define(Types.Inductive, xs, ds) }
  | CODEFINE; xs=id_tys; BY; option(SEMICOLON); ds=defs; DOT
    { Types.Define(Types.CoInductive, xs, ds) }
  | QUERY; f=metaterm; DOT
    { Types.Query(f) }
  | IMPORT; im=located(QSTRING);
    ws=loption(WITH; ws=import_withs {ws}); DOT
    { Types.Import(im.el, im.pos, ws) }
  | SPECIFICATION; spec=located(QSTRING); DOT
    { Types.Specification(spec.el, spec.pos) }
  | KKIND; tys=id_list; ki=knd; DOT
    { Types.Kind(List.map deloc_id tys, ki) }
  | TTYPE; cs=id_list; ty=ty; DOT
    { Types.Type(List.map deloc_id cs, ty) }
  | CLOSE; tys=aty_list; DOT
    { Types.Close(tys) }
  | SSPLIT; thm=loc_id;
    cs=loption(AS; cs=id_list {cs}); DOT
    { Types.SSplit(deloc_id thm, List.map deloc_id cs) }

%inline
import_withs:
  | ws=separated_nonempty_list(COMMA, x=id; DEFEQ; t=id {(x, t)})
    { ws }

common_command:
  | SET; a=id; b=id; DOT
    { Types.Set(a, Types.Str b) }
  | SET; a=id; n=NUM; DOT
    { Types.Set(a, Types.Int n) }
  | SET; a=id; s=QSTRING; DOT
    { Types.Set(a, Types.QStr s) }
  | SHOW; l=loc_id; DOT
    { Types.Show(deloc_id l) }
  | SUSPEND; predicate=loc_id; args=list(id); DEFEQ; flex=separated_nonempty_list(COMMA, id); DOT
    { let pos = $startpos in
      if not (List.is_unique args) then
        error_report ~pos "argument list is not unique: %s" (String.concat " " args) ;
      if not (List.is_unique flex) then
        error_report ~pos "flex list is not unique: %s" (String.concat " " flex) ;
      if List.exists (fun f -> not @@ List.mem f args) flex then
        error_report ~pos "flex list [%s] is not a subset of argument list [%s]"
          (String.concat " " flex) (String.concat " " args) ;
      let arity = List.length args in
      let flex = List.mapi (fun i x -> if List.mem x flex then i else -1) args
                 |> List.filter (fun x -> x >= 0) in
      Types.(Suspend { predicate ; arity ; flex }) }
  | QUIT; DOT
    { Types.Quit }
  | BACK; DOT
    { Types.Back }
  | RESET; DOT
    { Types.Reset }
  | EOF
    { raise End_of_file }

search_witness:
  | TRUE
    { Types.WTrue }
  | APPLY; x=id
    { Types.WHyp x }
  | LEFT; w=search_witness
    { Types.WLeft w }
  | RIGHT; w=search_witness
    { Types.WRight w }
  | SPLIT; LPAREN; w1=search_witness; COMMA; w2=search_witness; RPAREN
    { Types.WSplit (w1, w2) }
  | INTROS; LBRACK; xs=id_list; RBRACK; w=search_witness
    { Types.WIntros (List.map deloc_id xs, w) }
  | FORALL; LBRACK; xs=id_list; RBRACK; w=search_witness
    { Types.WForall (List.map deloc_id xs, w) }
  | EXISTS; LBRACK; ex=exists_binds; RBRACK; w=search_witness
    { Types.WExists (ex, w) }
  | UNFOLD; LPAREN; x=id; COMMA; n=NUM;
    ws=loption(COMMA; ws=separated_nonempty_list(COMMA, search_witness) {ws});
    RPAREN
    { Types.WUnfold (x, n, ws) }
  | STAR
    { Types.WMagic }
  | EQ
    { Types.WReflexive }
  | LPAREN; w=search_witness; RPAREN
    { w }

exists_binds:
  | { [] }
  | withs
    { List.map (fun (id, t) -> (id, uterm_to_term t)) $1 }

depth_spec:
  | ds=separated_nonempty_list(SEMICOLON, depth_spec_one) EOF
    { ds }

depth_spec_one:
  | n1=NUM; LBRACK; n2=NUM; RBRACK
    { (n1, Some n2) }
  | n=NUM
    { (n, None) }

one_term:
  | t=term EOF { t }
one_metaterm:
  | mt=metaterm EOF { mt }
one_sig_body:
  | bod=list(sig_decl) EOF { bod }
one_mod_body:
  | bod=list(mod_clause) EOF { bod }
one_defs:
  | ds=defs DOT EOF { ds }

cmdline_flags:
  | fls=separated_list(COMMA,cmdline_flag); EOF
    { fls }

cmdline_flag:
  | a=id            { cmdline_arg_one a }
  | a=id; q=QSTRING { cmdline_arg_two a @@ Abella_types.QStr q }

%inline
located(X):
  | x=X { { el = x ; pos = $loc } }
