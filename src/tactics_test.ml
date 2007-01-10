open OUnit
open Term
open Term.Notations
open Lppterm
open Tactics
  
let id x = x
  
let assert_pprint_equal s t =
  assert_equal ~printer:id s (lppterm_to_string t)

let parse str = Top_parser.lppterm Top_lexer.token (Lexing.from_string str)
    
let tests =
  "Tactics" >:::
    [
      "Simple object cut" >::
        (fun () ->
           let t = object_cut (parse "{A => B}") (parse "{A}") in
             assert_pprint_equal "{B}" t) ;
      
      "Compound object cut" >::
        (fun () ->
           let h0 = parse "{eval A B => typeof B C}" in
           let h1 = parse "{eval A B}" in
           let t = object_cut h0 h1 in
             assert_pprint_equal "{typeof B C}" t) ;

      "Simple object instantiation" >::
        (fun () ->
           let h0 = parse "{pi x\\ eval x B}" in
           let a = var ~tag:Eigen "A" 0 in
           let t = object_inst h0 a in
             assert_pprint_equal "{eval A B}" t) ;

      "Forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B} -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}" in
           let h2 = parse "{typeof (abs R) (arrow S T)}" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Properly restricted forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}* -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}*" in
           let h2 = parse "{typeof (abs R) (arrow S T)}" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Needlessly restricted forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B} -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}*" in
           let h2 = parse "{typeof (abs R) (arrow S T)}" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;
      
      "Improperly restricted forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}* -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}" in
           let h2 = parse "{typeof (abs R) (arrow S T)}" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "Improperly inactivated forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}* -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}@" in
           let h2 = parse "{typeof (abs R) (arrow S T)}" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "Unification failure during forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B} -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}" in
           let h2 = parse "{bad (abs R) (arrow S T)}" in
             assert_raises (Failure "Unification failure")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "Case application" >::
        (fun () ->
           (* eval (abs R) (abs R).
              eval (app M N) V :- eval M (abs R), eval (R N) V.

              case {eval A B} *)
           let str = "eval (abs R) (abs R).\n" ^
             "eval (app M N) V :- eval M (abs R), eval (R N) V." in
           let prog = Parser.clauses Lexer.token (Lexing.from_string str) in
           let a = var ~tag:Eigen "A" 0 in
           let b = var ~tag:Eigen "B" 0 in
           let term = obj (app (const "eval") [a; b]) in
             match case term prog ["A"; "B"] with
               | [(f1, v1, []); (f2, v2, [b1; b2])] ->
                   f1 () ;
                   assert_pprint_equal "{eval (abs R) (abs R)}" term ;
                   assert_bool "R should be flagged as used"
                     (List.mem "R" v1) ;
                   f2 () ;
                   assert_pprint_equal "{eval (app M N) B}" term ;
                   assert_pprint_equal "{eval M (abs R)}" b1 ;
                   assert_pprint_equal "{eval (R N) B}" b2 ;
                   assert_bool "R should be flagged as used"
                     (List.mem "R" v2) ;
                   assert_bool "M should be flagged as used"
                     (List.mem "M" v2) ;
                   assert_bool "N should be flagged as used"
                     (List.mem "N" v2)
               | _ -> assert_failure "Pattern mismatch") ;
      
      "Restricted case application" >::
        (fun () ->
           (* eval (abs R) (abs R).
              eval (app M N) V :- eval M (abs R), eval (R N) V.

              case {eval A B} which has inactive restriction 1 *)
           let str = "eval (abs R) (abs R).\n" ^
             "eval (app M N) V :- eval M (abs R), eval (R N) V." in
           let prog = Parser.clauses Lexer.token (Lexing.from_string str) in
           let a = var ~tag:Eigen "A" 0 in
           let b = var ~tag:Eigen "B" 0 in
           let term = inactive_obj (app (const "eval") [a; b]) 1 in
             match case term prog ["A"; "B"] with
               | [(f1, v1, []); (f2, v2, [b1; b2])] ->
                   f1 () ;
                   assert_pprint_equal "{eval (abs R) (abs R)}@" term ;
                   f2 () ;
                   assert_pprint_equal "{eval (app M N) B}@" term ;
                   assert_pprint_equal "{eval M (abs R)}*" b1 ;
                   assert_pprint_equal "{eval (R N) B}*" b2 
               | _ -> assert_failure "Pattern mismatch") ;

      "Single induction creation" >::
        (fun () ->
           let stmt = parse
               "forall A, {first A} -> {second A} -> {third A}" in
           let (ih, goal) = induction [1] stmt in
             assert_pprint_equal
               "forall A, {first A}* -> {second A} -> {third A}"
               ih ;
             assert_pprint_equal
               "forall A, {first A}@ -> {second A} -> {third A}"
               goal) ;
      
      "Double induction creation" >::
        (fun () ->
           let stmt = parse
               "forall A, {first A} -> {second A} -> {third A}" in
           let (ih, goal) = induction [1; 2] stmt in
             assert_pprint_equal
               "forall A, {first A}* -> {second A}** -> {third A}"
               ih ;
             assert_pprint_equal
               "forall A, {first A}@ -> {second A}@@ -> {third A}"
               goal) ;
      
    ]
