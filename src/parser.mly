/****************************************************************************/
/* Copyright (C) 2007-2009 Gacek                                            */
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

  open Typing

  module Types = Abella_types

  let pos i =
    if i = 0 then
      (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
    else
      (Parsing.rhs_start_pos i, Parsing.rhs_end_pos i)

  let predefined id =
    UCon(pos 0, id, Term.fresh_tyvar ())

  let binop id t1 t2 =
    UApp(pos 0, UApp(pos 0, predefined id, t1), t2)

  let nested_app head args =
    List.fold_left
      (fun h a -> UApp((fst (get_pos h), snd (get_pos a)), h, a))
      head args

%}

%token IMP COMMA DOT BSLASH LPAREN RPAREN TURN CONS EQ TRUE FALSE DEFEQ
%token IND INST APPLY CASE SEARCH TO ON WITH INTROS CUT ASSERT CLAUSEEQ
%token SKIP UNDO ABORT COIND LEFT RIGHT MONOTONE IMPORT BY
%token SPLIT SPLITSTAR UNFOLD KEEP CLEAR SPECIFICATION SEMICOLON
%token THEOREM DEFINE PLUS CODEFINE SET ABBREV UNABBREV QUERY SHOW
%token PERMUTE BACKCHAIN QUIT UNDERSCORE AS SSPLIT
%token COLON RARROW FORALL NABLA EXISTS STAR AT HASH OR AND LBRACK RBRACK
%token KIND TYPE KKIND TTYPE SIG MODULE ACCUMSIG ACCUM END CLOSE

%token <int> NUM
%token <string> STRINGID QSTRING
%token EOF

/* Lower */

%nonassoc COMMA
%right RARROW
%left OR
%left AND

%nonassoc BSLASH
%right IMP
%nonassoc EQ

%right CONS

/* Higher */


%start term metaterm lpmod lpsig defs top_command command any_command sig_body mod_body
%type <Typing.uterm> term
%type <Typing.umetaterm> metaterm
%type <Abella_types.lpsig> lpsig
%type <Abella_types.lpmod> lpmod
%type <Abella_types.sig_decl list> sig_body
%type <Abella_types.uclause list> mod_body
%type <Abella_types.udef list> defs
%type <Abella_types.command> command
%type <Abella_types.top_command> top_command
%type <Abella_types.any_command> any_command

%%

hyp:
  | STRINGID                             { $1 }
  | UNDERSCORE                           { "_" }

id:
  | STRINGID                             { $1 }
  | IND                                  { "induction" }
  | INST                                 { "inst" }
  | APPLY                                { "apply" }
  | BACKCHAIN                            { "backchain" }
  | CASE                                 { "case" }
  | SEARCH                               { "search" }
  | TO                                   { "to" }
  | ON                                   { "on" }
  | BY                                   { "by" }
  | AS                                   { "as" }
  | WITH                                 { "with" }
  | INTROS                               { "intros" }
  | CUT                                  { "cut" }
  | ASSERT                               { "assert" }
  | SKIP                                 { "skip" }
  | UNDO                                 { "undo" }
  | ABORT                                { "abort" }
  | COIND                                { "coinduction" }
  | LEFT                                 { "left" }
  | RIGHT                                { "right" }
  | MONOTONE                             { "monotone" }
  | SPLIT                                { "split" }
  | UNFOLD                               { "unfold" }
  | KEEP                                 { "keep" }
  | CLEAR                                { "clear" }
  | ABBREV                               { "abbrev" }
  | UNABBREV                             { "unabbrev" }
  | PERMUTE                              { "permute" }
  | THEOREM                              { "Theorem" }
  | IMPORT                               { "Import" }
  | SPECIFICATION                        { "Specification" }
  | DEFINE                               { "Define" }
  | CODEFINE                             { "CoDefine" }
  | SET                                  { "Set" }
  | SHOW                                 { "Show" }
  | QUIT                                 { "Quit" }
  | QUERY                                { "Query" }
  | SSPLIT                               { "Split" }
  | CLOSE                                { "Close" }
  | TTYPE                                { "Type" }
  | KKIND                                { "Kind" }

/* Annotated ID */
aid:
  | id                                   { ($1, Term.fresh_tyvar ()) }
  | id COLON ty                          { ($1, $3) }

/* Parenthesized annotated ID */
paid:
  | id                                   { ($1, Term.fresh_tyvar ()) }
  | LPAREN id COLON ty RPAREN            { ($2, $4) }
  | UNDERSCORE                           { ("_", Term.fresh_tyvar ()) }
  | LPAREN UNDERSCORE COLON ty RPAREN    { ("_", $4) }

contexted_term:
  | context TURN term                    { ($1, $3) }
  | term                                 { (predefined "nil", $1) }

context:
  | context COMMA term                   { binop "::" $3 $1 }
  | term                                 { if has_capital_head $1 then
                                             $1
                                           else
                                             binop "::" $1
                                               (predefined "nil") }

term:
  | term IMP term                        { binop "=>" $1 $3 }
  | term CONS term                       { binop "::" $1 $3 }
  | aid BSLASH term                      { let (id, ty) = $1 in
                                             ULam(pos 0, id, ty, $3) }
  | exp exp_list                         { nested_app $1 $2 }
  | exp                                  { $1 }

exp:
  | LPAREN term RPAREN                   { let left = fst (pos 1) in
                                           let right = snd (pos 3) in
                                             change_pos (left, right) $2 }
  | paid                                 { let (id, ty) = $1 in
                                             UCon(pos 0, id, ty) }

exp_list:
  | exp exp_list                         { $1::$2 }
  | exp                                  { [$1] }
  | aid BSLASH term                      { let (id, ty) = $1 in
                                             [ULam(pos 0, id, ty, $3)] }

lpsig:
  | sig_header sig_preamble sig_body lpend
                                         { Types.Sig($1, $2, $3) }

sig_header:
  | SIG id DOT                           { $2 }

sig_preamble:
  | ACCUMSIG id_list DOT sig_preamble    { $2 @ $4 }
  |                                      { [] }

sig_body:
  | KIND id_list TYPE DOT sig_body       { Types.SKind($2) :: $5 }
  | TYPE id_list ty DOT sig_body         { Types.SType($2, $3) :: $5 }
  |                                      { [] }

lpmod:
  | mod_header mod_preamble mod_body lpend
                                         { Types.Mod($1, $2, $3) }

mod_header:
  | MODULE id DOT                        { $2 }

mod_preamble:
  | ACCUM id_list DOT mod_preamble       { $2 @ $4 }
  |                                      { [] }

mod_body:
  | clause mod_body                      { $1::$2 }
  |                                      { [] }

lpend:
  | END                                  { }
  |                                      { }

id_list:
  | id                                   { [$1] }
  | id COMMA id_list                     { $1::$3}

ty:
  | id                                   { Term.tybase $1 }
  | ty RARROW ty                         { Term.tyarrow [$1] $3 }
  | LPAREN ty RPAREN                     { $2 }

clause:
  | term DOT                             { ($1, []) }
  | term CLAUSEEQ clause_body DOT        { ($1, $3) }

clause_body:
  | term COMMA clause_body               { $1::$3 }
  | LPAREN term COMMA clause_body RPAREN { $2::$4 }
  | term                                 { [$1] }

defs:
  | def SEMICOLON defs                   { $1::$3 }
  | def                                  { [$1] }

def:
  | metaterm                             { ($1, UTrue) }
  | metaterm DEFEQ metaterm              { ($1, $3) }

perm:
  | LPAREN perm_ids RPAREN               { $2 }

perm_ids:
  | id perm_ids                          { $1 :: $2 }
  | id                                   { [$1] }

any_command:
  | pure_top_command                     { Types.ATopCommand($1) }
  | pure_command                         { Types.ACommand($1) }
  | common_command                       { Types.ACommon($1) }

command:
  | pure_command                         { $1 }
  | common_command                       { Types.Common($1) }

pure_command:
  | hhint IND ON num_list DOT                 { Types.Induction($4, $1) }
  | hhint COIND DOT                           { Types.CoInduction($1) }
  | hhint APPLY id TO hyp_list DOT            { Types.Apply($3, $5, [], $1) }
  | hhint APPLY id TO hyp_list WITH withs DOT { Types.Apply($3, $5, $7, $1) }
  | hhint APPLY id WITH withs DOT             { Types.Apply($3, [], $5, $1) }
  | hhint APPLY id DOT                        { Types.Apply($3, [], [], $1) }
  | BACKCHAIN id DOT                          { Types.Backchain($2, []) }
  | BACKCHAIN id WITH withs DOT               { Types.Backchain($2, $4) }
  | hhint CUT hyp WITH hyp DOT                { Types.Cut($3, $5, $1) }
  | hhint CUT hyp DOT                         { Types.SearchCut($3, $1) }
  | hhint INST hyp WITH withs DOT             { Types.Inst($3, $5, $1) }
  | hhint CASE hyp DOT                        { Types.Case($3, false, $1) }
  | hhint CASE hyp LPAREN KEEP RPAREN DOT     { Types.Case($3, true, $1) }
  | hhint ASSERT metaterm DOT                 { Types.Assert($3, $1) }
  | EXISTS term DOT                           { Types.Exists($2) }
  | SEARCH DOT                                { Types.Search(None) }
  | SEARCH NUM DOT                            { Types.Search(Some $2) }
  | SPLIT DOT                                 { Types.Split }
  | SPLITSTAR DOT                             { Types.SplitStar }
  | LEFT DOT                                  { Types.Left }
  | RIGHT DOT                                 { Types.Right }
  | INTROS DOT                                { Types.Intros [] }
  | INTROS hyp_list DOT                       { Types.Intros($2) }
  | SKIP DOT                                  { Types.Skip }
  | ABORT DOT                                 { Types.Abort }
  | UNDO DOT                                  { Types.Undo }
  | UNFOLD DOT                                { Types.Unfold }
  | CLEAR hyp_list DOT                        { Types.Clear($2) }
  | ABBREV hyp QSTRING DOT                    { Types.Abbrev($2, $3) }
  | UNABBREV hyp_list DOT                     { Types.Unabbrev($2) }
  | MONOTONE hyp WITH term DOT                { Types.Monotone($2, $4) }
  | PERMUTE perm DOT                          { Types.Permute($2, None) }
  | PERMUTE perm hyp DOT                      { Types.Permute($2, Some $3) }

hhint:
  | STRINGID COLON                       { Some $1 }
  |                                      { None }

hyp_list:
  | hyp hyp_list                         { $1::$2 }
  | hyp                                  { [$1] }

num_list:
  | NUM num_list                         { $1::$2 }
  | NUM                                  { [$1] }

withs:
  | id EQ term COMMA withs               { ($1, $3) :: $5 }
  | id EQ term                           { [($1, $3)] }

metaterm:
  | TRUE                                 { UTrue }
  | FALSE                                { UFalse }
  | term EQ term                         { UEq($1, $3) }
  | binder binding_list COMMA metaterm   { UBinding($1, $2, $4) }
  | metaterm RARROW metaterm             { UArrow($1, $3) }
  | metaterm OR metaterm                 { UOr($1, $3) }
  | metaterm AND metaterm                { UAnd($1, $3) }
  | LPAREN metaterm RPAREN               { $2 }
  | LBRACK contexted_term RBRACK restriction
                                         { let l, g = $2 in
                                             UObj(l, g, $4) }
  | term restriction                     { UPred($1, $2) }

binder:
  | FORALL                               { Metaterm.Forall }
  | EXISTS                               { Metaterm.Exists }
  | NABLA                                { Metaterm.Nabla }

binding_list:
  | paid binding_list                    { $1::$2 }
  | paid                                 { [$1] }

restriction:
  |                                      { Metaterm.Irrelevant }
  | stars                                { Metaterm.Smaller $1 }
  | pluses                               { Metaterm.CoSmaller $1 }
  | ats                                  { Metaterm.Equal $1 }
  | hashes                               { Metaterm.CoEqual $1 }

stars:
  | STAR stars                           { 1 + $2 }
  | STAR                                 { 1 }

ats:
  | AT ats                               { 1 + $2 }
  | AT                                   { 1 }

pluses:
  | PLUS pluses                          { 1 + $2 }
  | PLUS                                 { 1 }

hashes:
  | HASH hashes                          { 1 + $2 }
  | HASH                                 { 1 }

id_ty:
  | id COLON ty                          { ($1, $3) }

id_tys:
  | id_ty COMMA id_tys                   { $1::$3 }
  | id_ty                                { [$1] }

top_command:
  | pure_top_command                     { $1 }
  | common_command                       { Types.TopCommon($1) }

pure_top_command:
  | THEOREM id COLON metaterm DOT        { Types.Theorem($2, $4) }
  | DEFINE id_tys BY defs DOT            { Types.Define($2, $4) }
  | CODEFINE id_tys BY defs DOT          { Types.CoDefine($2, $4) }
  | QUERY metaterm DOT                   { Types.Query($2) }
  | IMPORT QSTRING DOT                   { Types.Import($2) }
  | SPECIFICATION QSTRING DOT            { Types.Specification($2) }
  | KKIND id_list TYPE DOT               { Types.Kind($2) }
  | TTYPE id_list ty DOT                 { Types.Type($2, $3) }
  | CLOSE id_list DOT                    { Types.Close($2) }
  | SSPLIT id DOT                        { Types.SSplit($2, []) }
  | SSPLIT id AS id_list DOT             { Types.SSplit($2, $4) }

common_command:
  | SET id id DOT                        { Types.Set($2, Types.Str $3) }
  | SET id NUM DOT                       { Types.Set($2, Types.Int $3) }
  | SHOW id DOT                          { Types.Show($2) }
  | QUIT DOT                             { Types.Quit }
  | EOF                                  { raise End_of_file }
