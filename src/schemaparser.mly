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

  module Types = Schema_types

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

%token IMP COMMA DOT BSLASH LPAREN RPAREN TURN CONS EQ TRUE FALSE DEFEQ BANG
%token SCHEMA INVERSION PROJECTION SYNC UNIQUE
%token SEMICOLON UNDERSCORE
%token COLON RARROW FORALL NABLA EXISTS 
%token LBRACE RBRACE LBRACK RBRACK

%token <string> STRINGID QSTRING
%token EOF

/* Lower */

%nonassoc COMMA
%right RARROW

%nonassoc BSLASH
%right IMP
%nonassoc EQ

%right CONS

/* Higher */


%start term top_command command
%type <Typing.uterm> term
%type <Schema_types.top_command> top_command
%type <Schema_types.command> command

%%

hyp:
  | STRINGID                             { $1 }

id:
  | STRINGID                             { $1 }
  | SCHEMA                               { "Schema" }
  | PROJECTION                           { "projas" }
  | UNIQUE                               { "unique" }
  | SYNC                                 { "sync"}
  | INVERSION                            { "inversion"}

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



sclause_list:
  | existsopt nablaopt term_tup                { [($1,$2,$3)] }
  | existsopt nablaopt term_tup SEMICOLON sclause_list  { ($1,$2,$3)::$5}


term_tup:
  | term                                 { [$1] }
  | LPAREN term_list RPAREN              { $2   }

term_list:
  | term                                 { [$1] }
  | term COMMA term_list                 { $1::$3}

id_list:
  | id                                   { [$1] }
  | id COMMA id_list                     { $1::$3}

ty:
  | id                                   { Term.tybase $1 }
  | ty RARROW ty                         { Term.tyarrow [$1] $3 }
  | LPAREN ty RPAREN                     { $2 }


existsopt:
  | EXISTS utbinding_list COMMA            { $2 }
  |                                      { [] }

nablaopt:
  | NABLA utbinding_list COMMA            { $2 }
  |                                      { [] }

utbinding_list:
  | id utbinding_list                    { $1::$2 }
  | id                                 { [$1] }




perm_ids:
  | id perm_ids                          { $1 :: $2 }
  | id                                   { [$1] }

hyp_list:
  | hyp hyp_list                         { $1::$2 }
  | hyp                                  { [$1] }

command:
  | INVERSION hyp_list DOT                    { Schema_types.Inversion($2)}
  | PROJECTION LPAREN perm_ids RPAREN hyp_list DOT    { Schema_types.Projection($3,$5)}
  | UNIQUE hyp_list DOT                       { Schema_types.Unique($2)}
  | SYNC hyp_list DOT                         { Schema_types.Sync($2)}
  | EOF                                       { raise End_of_file }

top_command:
  | SCHEMA id DEFEQ sclause_list DOT          { Schema_types.SchemaDef($2,$4) }
  | EOF                                       { raise End_of_file }


