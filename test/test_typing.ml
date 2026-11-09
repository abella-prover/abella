open Abella_lib
open Extensions
open Test_helper
open Typing
open Term
open Metaterm

let dummy_pos = (Lexing.dummy_pos, Lexing.dummy_pos)

let ucon ?(ty=fresh_tyvar ()) v =
  UCon(dummy_pos, v, ty)

let ulam v ?(ty=fresh_tyvar ()) t =
  ULam(dummy_pos, v, ty, t)

let uapp t1 t2 =
  UApp(dummy_pos, t1, t2)

let upred t =
  UPred(t, Irrelevant)

type uterm =
  | UCon of pos * string * ty
  | ULam of pos * string * ty * uterm
  | UApp of pos * uterm * uterm


let tests =
  suite "Typing" [
      test_case "Should not allow pi quantification over o in clause"
        (fun () ->
           let uclause =
             (None, ucon "a", [uapp (ucon "pi") (ulam "x" ~ty:oty (ucon "x"))])
           in
             Alcotest.check_raises
               "Cannot quantify over type o in the specification logic"
               (Failure
                  "Cannot quantify over type o in the specification logic")
               (fun () ->
                  ignore (type_uclause ~sr:!sr ~sign:!sign uclause))
        );

      test_case "Should not allow quantification over prop in definition"
        (fun () ->
           let udef =
             (UTrue, UBinding(Forall, [("x", propty)], upred (ucon "x")))
           in
             Alcotest.check_raises
               "Cannot quantify over type prop"
               (Failure "Cannot quantify over type prop")
               (fun () -> ignore (type_udef ~sr:!sr ~sign:!sign udef))
        );

      test_case "Should not allow quantification over prop in metaterm"
        (fun () ->
           let umetaterm =
             UBinding(Forall, [("x", propty)], upred (ucon "x"))
           in
             Alcotest.check_raises
               "Cannot quantify over type prop"
               (Failure "Cannot quantify over type prop")
               (fun () -> ignore (type_umetaterm ~sr:!sr ~sign:!sign umetaterm))
        );

      test_case "Should not instantiate schematic types with prop"
        (fun () ->
           let saved = !schematic_instantiations in
           schematic_instantiations := [] ;
           Fun.protect ~finally:(fun () ->
             schematic_instantiations := saved) begin fun () ->
             ignore (parse_metaterm "poly russell_d") ;
             Alcotest.check_raises
               "Schematic instantiation with prop"
               (Failure "Schematic type variable A cannot be instantiated \
                         with prop")
               (fun () -> Checks.ensure_no_prop_schematic_instantiation ())
           end
        );

      test_case "Should not instantiate schematic types with prop inside"
        (fun () ->
           let saved = !schematic_instantiations in
           schematic_instantiations := [] ;
           Fun.protect ~finally:(fun () ->
             schematic_instantiations := saved) begin fun () ->
             ignore (parse_metaterm "poly ho_decl") ;
             Alcotest.check_raises
               "Schematic instantiation with type containing prop"
               (Failure "Schematic type variable A cannot be instantiated \
                         with (prop -> prop) -> prop, which contains prop")
               (fun () -> Checks.ensure_no_prop_schematic_instantiation ())
           end
        );

      test_case "Should allow schematic instantiation without prop"
        (fun () ->
           let saved = !schematic_instantiations in
           schematic_instantiations := [] ;
           Fun.protect ~finally:(fun () ->
             schematic_instantiations := saved) begin fun () ->
             ignore (parse_metaterm "poly t1") ;
             Checks.ensure_no_prop_schematic_instantiation () ;
             Alcotest.check (Alcotest.list (Alcotest.pair
               Alcotest.string ty_testable))
               "instantiations should be pruned" []
               !schematic_instantiations
           end
        );

      test_case "Should not compare terms of type prop with equality"
        (fun () ->
           Alcotest.check_raises
             "Equality over prop"
             (Failure
                "Equality cannot be used to compare terms of type prop")
             (fun () -> ignore (parse_metaterm "russell_d = russell_d"))
        );

      test_case "Should not compare terms of prop-containing type"
        (fun () ->
           Alcotest.check_raises
             "Equality over type containing prop"
             (Failure "Equality cannot be used to compare terms of type \
                       (prop -> prop) -> prop, which contains prop")
             (fun () -> ignore (parse_metaterm "ho_decl = ho_decl"))
        );

      test_case "Should compare terms of first-order types with equality"
        (fun () ->
           ignore (parse_metaterm "t1 = t2") ;
           ignore (parse_metaterm "r1 t1 = r2 t2")
        );

      test_case "Should compare terms of schematic types with equality"
        (fun () ->
           let x = Term.const "X" (Term.tybase (Term.Tygenvar "A")) in
           Typing.ensure_no_prop_equality (Metaterm.Eq (x, x))
        );

      test_case "Should replace underscores in clauses with fresh names"
        (fun () ->
           let uclause =
             (None,
              uapp (ucon "p1") (ucon "X"),
              [uapp (uapp (ucon "pr") (ucon "_")) (ucon "_")])
           in
             let (_, clause) = type_uclause ~sr:!sr ~sign:!sign uclause in
             match Metaterm.clausify clause with
               | [_, _, p::_] ->
                   assert_term_pprint_equal "pr X1 X2" p
               | _ -> assert false
        );

      test_case "Type parameters keep first-occurrence order"
        (fun () ->
           let a = tybase (Tygenvar "A") in
           let b = tybase (Tygenvar "B") in
           let ty = tyarrow [b; a; b; a] propty in
             Alcotest.check (Alcotest.list Alcotest.string)
               "type parameters differ" ["B"; "A"] (get_typaram ty)
        );

      test_case "Type and definition schemes agree"
        (fun () ->
           let a = tybase (Tygenvar "A") in
           let ty = tyarrow [a; a] propty in
           let scheme =
             List.assoc "item3_eq" (snd (add_consts !sign [("item3_eq", ty)]))
           in
           let define_scheme =
             Poly (List.unique (get_typarams [ty]), ty)
           in
             Alcotest.check Alcotest.bool "schemes differ" true
               (eq_pty scheme define_scheme) ;
             match scheme with
             | Poly(ids, _) ->
                 Alcotest.check (Alcotest.list Alcotest.string)
                   "type parameters differ" ["A"] ids
        );

      test_case "Unused type parameters are not invented"
        (fun () ->
           let a = tybase (Tygenvar "A") in
           let ty = tyarrow [a] propty in
             Alcotest.check (Alcotest.list Alcotest.string)
               "type parameters differ" ["A"] (get_typaram ty) ;
             Alcotest.check Alcotest.bool "unused parameter invented" false
               (List.mem "B" (get_typaram ty))
        );
    ]
