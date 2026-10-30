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
    ]
