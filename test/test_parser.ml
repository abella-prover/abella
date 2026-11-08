open Test_helper
open Abella_lib
open Typing

let assert_uterm_pprint_equal s t =
  Alcotest.check Alcotest.string "strings differ" s (uterm_to_string t)

let assert_umetaterm_pprint_equal s t =
  Alcotest.check Alcotest.string "strings differ" s (umetaterm_to_string t)

let assert_pprint_equal_parse str =
  assert_umetaterm_pprint_equal str (parse_umetaterm str)

let parse_command str =
  Parser.command_start Lexer.token (Lexing.from_string str)

let assert_top_pprint expected str =
  Alcotest.check Alcotest.string "top command printing" expected
    (Abella_types.top_command_to_string (parse_top_command str).el)

let assert_command_pprint expected str =
  Alcotest.check Alcotest.string "command printing" expected
    (Abella_types.command_to_string (parse_command str).el)

let assert_rejected str =
  match parse_top_command str with
  | _ -> Alcotest.failf "%S unexpectedly parsed" str
  | exception _ -> ()

let qid_string = Abella_types.qualid_to_string

let source_string = function
  | Abella_types.QuoteSource (filename, _) -> "file:" ^ filename
  | Abella_types.NameSource name -> "name:" ^ name

let assert_module str name params =
  match (parse_top_command str).el with
  | Abella_types.Module (actual_name, actual_params) ->
      Alcotest.check Alcotest.string "module name" name actual_name ;
      Alcotest.check (Alcotest.list Alcotest.string) "parameters"
        params actual_params
  | _ -> Alcotest.failf "%S is not a module" str

let assert_end str name =
  match (parse_top_command str).el with
  | Abella_types.End actual_name ->
      Alcotest.check Alcotest.string "module name" name actual_name
  | _ -> Alcotest.failf "%S is not an end" str

let assert_import_module str alias source tyargs withs =
  match (parse_top_command str).el with
  | Abella_types.ImportModule mi ->
      let actual_alias =
        match mi.mi_alias with None -> "" | Some name -> name
      in
      Alcotest.check Alcotest.string "alias" alias actual_alias ;
      Alcotest.check Alcotest.string "source" source
        (source_string mi.mi_source) ;
      Alcotest.check (Alcotest.list Alcotest.string) "type arguments"
        tyargs (List.map Term.ty_to_string mi.mi_tyargs) ;
      Alcotest.check
        (Alcotest.list
           (Alcotest.pair Alcotest.string Alcotest.string))
        "with clauses" withs
        (List.map (fun (k, v) -> (qid_string k, qid_string v))
           mi.mi_withs)
  | _ -> Alcotest.failf "%S is not an import module" str

let tests =
  suite "Parser" [
      test_case "Empty bodied clause"
        (fun () ->
           let str = "eval (abs R) (abs R)." in
             match parse_uclauses str with
               | [{ el = (None, t, []) ; _ }] ->
                   assert_uterm_pprint_equal "eval (abs R) (abs R)" t
               | _ -> Alcotest.fail "Pattern mismatch" ) ;

      test_case "Typical clause"
        (fun () ->
           let str = "eval (app M N) V :- eval M (abs R), eval (R N) V." in
             match parse_uclauses str with
               | [{ el = (None, head, [b1; b2]) ; _ }] ->
                   assert_uterm_pprint_equal "eval (app M N) V" head ;
                   assert_uterm_pprint_equal "eval M (abs R)" b1 ;
                   assert_uterm_pprint_equal "eval (R N) V" b2 ;
               | _ -> Alcotest.fail "Pattern mismatch" ) ;

      test_case "Infix cons"
        (fun () ->
           assert_pprint_equal_parse "{member A (A :: B :: L)}") ;

      test_case "Simple object statement"
        (fun () ->
           assert_pprint_equal_parse "{eval A B}") ;

      test_case "Compound object statement"
        (fun () ->
           assert_pprint_equal_parse "{eval (abs R) (abs R)}") ;

      test_case "Implication object statement"
        (fun () ->
           assert_pprint_equal_parse "{eval A B => typeof C D}") ;

      test_case "Lambda object statement"
        (fun () ->
           assert_pprint_equal_parse "{x1\\typeof x1 A}") ;

      test_case "Pi lambda object statement"
        (fun () ->
           assert_pprint_equal_parse "{pi x1\\typeof x1 A}") ;

      test_case "Pi lambda implies object statement"
        (fun () ->
           assert_pprint_equal_parse "{pi x1\\eval x1 A => typeof x1 B}") ;

      test_case "Lambda cons"
        (fun () ->
           assert_pprint_equal_parse "x1\\a :: b") ;

      test_case "Cons equality"
        (fun () ->
           assert_pprint_equal_parse "a :: b = a :: b") ;

      test_case "Smaller restriction"
        (fun () ->
           assert_pprint_equal_parse "{A}*") ;

      test_case "CoSmaller restriction"
        (fun () ->
           assert_pprint_equal_parse "foo +") ;

      test_case "CoEqual restriction"
        (fun () ->
           assert_pprint_equal_parse "foo #") ;

      test_case "Equal restriction"
        (fun () ->
           assert_pprint_equal_parse "{A}@") ;

      test_case "Second smaller restriction"
        (fun () ->
           assert_pprint_equal_parse "{A}**") ;

      test_case "Smaller restriction on predicate"
        (fun () ->
           assert_pprint_equal_parse "pred A B *") ;

      test_case "Implies statement"
        (fun () ->
           assert_pprint_equal_parse "{A} -> {B}") ;

      test_case "OR statement"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B}") ;

      test_case "AND statement"
        (fun () ->
           assert_pprint_equal_parse "{A} /\\ {B}") ;

      test_case "AND within OR"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B} /\\ {C}") ;

      test_case "OR statement on right side of arrow"
        (fun () ->
           assert_pprint_equal_parse "{A} -> {B} \\/ {C}") ;

      test_case "OR statement on left side of arrow"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B} -> {C}") ;

      test_case "Multiple OR statement"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B} \\/ {C}") ;

      test_case "Multiple OR statement (right assoc)"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ ({B} \\/ {C})") ;

      test_case "Arrow underneath OR"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ ({B} -> {C})") ;

      test_case "Forall"
        (fun () ->
           assert_pprint_equal_parse "forall A B, {C}") ;

      test_case "Exists"
        (fun () ->
           assert_pprint_equal_parse "exists A B, {C}") ;

      test_case "Exists on left of OR"
        (fun () ->
           assert_pprint_equal_parse "(exists A, {B}) \\/ {C}") ;

      test_case "OR underneath exists"
        (fun () ->
           assert_pprint_equal_parse "exists A, {B} \\/ {C}") ;

      test_case "Variable in context"
        (fun () ->
           assert_pprint_equal_parse "{L |- A}") ;

      test_case "Simple predicate"
        (fun () ->
           assert_pprint_equal_parse "head A B") ;

      test_case "Complex predicate"
        (fun () ->
           assert_pprint_equal_parse "head (hyp A) (conc B)") ;

      test_case "Module without parameters"
        (fun () ->
           assert_module "Module Foo." "Foo" []) ;

      test_case "Module with one parameter"
        (fun () ->
           assert_module "Module Box[T]." "Box" ["T"]) ;

      test_case "Module with several parameters"
        (fun () ->
           assert_module "Module Box[T, U]." "Box" ["T"; "U"]) ;

      test_case "End"
        (fun () ->
           assert_end "End Foo." "Foo") ;

      test_case "Empty module parameter list is rejected"
        (fun () ->
           assert_rejected "Module Foo[].") ;

      test_case "Lowercase module parameter is rejected"
        (fun () ->
           assert_rejected "Module Foo[a].") ;

      test_case "Duplicate module parameters are rejected"
        (fun () ->
           assert_rejected "Module Foo[T, T].") ;

      test_case "Import module quoted without arguments"
        (fun () ->
           assert_import_module "Import Module \"Foo\"."
             "" "file:Foo" [] []) ;

      test_case "Import module quoted with arguments"
        (fun () ->
           assert_import_module "Import Module \"Foo\"[nat]."
             "" "file:Foo" ["nat"] []) ;

      test_case "Import module quoted with several arguments"
        (fun () ->
           assert_import_module "Import Module \"lib/Foo\"[nat, list nat]."
             "" "file:lib/Foo" ["nat" ; "list nat"] []) ;

      test_case "Import module unquoted"
        (fun () ->
           assert_import_module "Import Module Foo."
             "" "name:Foo" [] []) ;

      test_case "Import module with quoted alias and arguments"
        (fun () ->
           assert_import_module "Import Module L = \"Foo\"[nat]."
             "L" "file:Foo" ["nat"] []) ;

      test_case "Import module with unquoted alias and arguments"
        (fun () ->
           assert_import_module "Import Module L = Foo[nat, bool]."
             "L" "name:Foo" ["nat" ; "bool"] []) ;

      test_case "Import module with simple with clause"
        (fun () ->
           assert_import_module "Import Module Foo with p := q."
             "" "name:Foo" [] [("p", "q")]) ;

      test_case "Import module with qualified with clause"
        (fun () ->
           assert_import_module
             "Import Module Baz = Foo[nat] with Bar.p := Baz.q, ax := thm."
             "Baz" "name:Foo" ["nat"]
             [("Bar.p", "Baz.q") ; ("ax", "thm")]) ;

      test_case "Empty import argument list is rejected"
        (fun () ->
           assert_rejected "Import Module \"Foo\"[].") ;

      test_case "Empty with clause is rejected"
        (fun () ->
           assert_rejected "Import Module Foo with.") ;

      test_case "Dotted import target is rejected"
        (fun () ->
           assert_rejected "Import Module Foo.Bar.") ;

      test_case "Alias brackets on the left are rejected"
        (fun () ->
           assert_rejected "Import Module Baz[nat] = Foo.") ;

      test_case "Module printing"
        (fun () ->
           assert_top_pprint "Module Box[T, U]" "Module Box[T, U].") ;

      test_case "End printing"
        (fun () ->
           assert_top_pprint "End Box" "End Box.") ;

      test_case "Import module printing"
        (fun () ->
           assert_top_pprint
             "Import Module Baz = \"lib/Foo\"[nat, list nat] with p := q"
             "Import Module Baz = \"lib/Foo\"[nat, list nat] with p := q.") ;

      test_case "Qualified term name"
        (fun () ->
           assert_uterm_pprint_equal "Foo.x" (parse_uterm "Foo.x")) ;

      test_case "Dotted qualified term name"
        (fun () ->
           assert_uterm_pprint_equal "Foo.Bar.x"
             (parse_uterm "Foo.Bar.x")) ;

      test_case "Annotated qualified term name"
        (fun () ->
           match parse_uterm "(Foo.x : i)" with
           | UCon (_, "Foo.x", ty) ->
               Alcotest.check Alcotest.string "annotated type"
                 "i" (Term.ty_to_string ty)
           | _ -> Alcotest.fail "Not an annotated constant") ;

      test_case "Qualified type name"
        (fun () ->
           match (parse_top_command "Type c Foo.u.").el with
           | Abella_types.Type (ids, ty) ->
               Alcotest.check (Alcotest.list Alcotest.string)
                 "declared names" ["c"] ids ;
               Alcotest.check Alcotest.string "declared type"
                 "Foo.u" (Term.ty_to_string ty)
           | _ -> Alcotest.fail "Not a Type command") ;

      test_case "Qualified type constructor argument"
        (fun () ->
           match (parse_top_command "Type c list Foo.u.").el with
           | Abella_types.Type (_, ty) ->
               Alcotest.check Alcotest.string "declared type"
                 "list Foo.u" (Term.ty_to_string ty)
           | _ -> Alcotest.fail "Not a Type command") ;

      test_case "Qualified name in unfold"
        (fun () ->
           assert_command_pprint "unfold Foo.thm"
             "unfold Foo.thm.") ;

      test_case "Qualified name in apply"
        (fun () ->
           assert_command_pprint "apply Foo.thm"
             "apply Foo.thm.") ;

      test_case "Qualified name in Show"
        (fun () ->
           assert_top_pprint "Show Foo.x" "Show Foo.x.") ;

      test_case "Show Module file"
        (fun () ->
           assert_top_pprint "Show Module \"List\""
             "Show Module \"List\".") ;

      test_case "Show Module name"
        (fun () ->
           assert_top_pprint "Show Module Foo"
             "Show Module Foo.") ;

      test_case "Show Module in proof"
        (fun () ->
           assert_command_pprint "Show Module Foo"
             "Show Module Foo.") ;

      test_case "Qualified name in Split"
        (fun () ->
           assert_top_pprint "Split Foo.thm" "Split Foo.thm.") ;

      test_case "Qualified names are single lexical tokens"
        (fun () ->
           let lexbuf = Lexing.from_string "Foo.Bar.x" in
           match Lexer.token lexbuf with
           | Parser.QUALID ["Foo" ; "Bar" ; "x"] -> ()
           | _ -> Alcotest.fail "Expected one qualified token") ;

      test_case "A dot before a keyword is part of a qualified name"
        (fun () ->
           let lexbuf = Lexing.from_string "P.Theorem" in
           match Lexer.token lexbuf with
           | Parser.QUALID ["P" ; "Theorem"] -> ()
           | _ -> Alcotest.fail "Expected one qualified token") ;

      test_case "A command terminator is not part of a qualified name"
        (fun () ->
           let lexbuf = Lexing.from_string "Foo . x" in
           let rec tokens acc =
             match Lexer.token lexbuf with
             | Parser.EOF -> List.rev acc
             | token -> tokens (token :: acc)
           in
           match tokens [] with
           | [Parser.STRINGID "Foo" ; Parser.DOT ;
              Parser.STRINGID "x"] -> ()
           | _ -> Alcotest.fail "Expected three tokens") ;

      test_case "Old single-name hint"
        (fun () ->
           assert_command_pprint "H : case H1" "H : case H1.") ;

      test_case "Single hspec alternative"
        (fun () ->
           assert_command_pprint "!U H : case H1" "!U H : case H1.") ;

      test_case "Multiple hspec alternatives"
        (fun () ->
           assert_command_pprint
             "[!U !V H1 | !U H1 H2] : case H1"
             "[ !U !V H1 | !U H1 H2 ] : case H1.") ;

      test_case "Don't-care hspec hints"
        (fun () ->
           assert_command_pprint
             "!U !_ H _ : case H1"
             "[ !U !_ H _ ] : case H1.") ;

      test_case "Empty hspec in brackets"
        (fun () ->
           assert_command_pprint "[ | H] : case H1"
             "[ | H ] : case H1.") ;

      test_case "Empty hspec normalizes away"
        (fun () ->
           assert_command_pprint "case H1" ": case H1.") ;

      test_case "Intros with no hints"
        (fun () ->
           assert_command_pprint "intros" "intros.") ;

      test_case "Intros with hypothesis hints"
        (fun () ->
           assert_command_pprint "intros H1 H2" "intros H1 H2.") ;

      test_case "Intros with variable hints"
        (fun () ->
           assert_command_pprint "intros !X H" "intros !X H.") ;

      test_case "Intros with don't-care hints"
        (fun () ->
           assert_command_pprint "intros !_ _ H" "intros !_ _ H.") ;

      test_case "Intros with a nominal variable hint"
        (fun () ->
           assert_command_pprint "intros !n34 H" "intros !n34 H.") ;

      test_case "Coinduction with a hint"
        (fun () ->
           assert_command_pprint "CH : coinduction" "CH : coinduction.") ;

    ]
