open OUnit
open Test_helper
open Typing
open Term
open Metaterm
open Prover (* Need global signature *)

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
  "Typing" >:::
    [
      "Should not allow quantification over prop in definition" >::
        (fun () ->
           let udef =
             (UTrue, UBinding(Forall, [("x", propty)], upred (ucon "x")))
           in
             assert_raises
               (Failure "Cannot quantify over type prop")
               (fun () -> type_udef ~sr:!sr ~sign:!sign udef)
        );

      "Should not allow quantification over prop in metaterm" >::
        (fun () ->
           let umetaterm =
             UBinding(Forall, [("x", propty)], upred (ucon "x"))
           in
             assert_raises
               (Failure "Cannot quantify over type prop")
               (fun () -> type_umetaterm ~sr:!sr ~sign:!sign umetaterm)
        );
    ]
