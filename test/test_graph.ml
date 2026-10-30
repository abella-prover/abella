open Test_helper
open Abella_lib
open Extensions
open Graph

let make_graph arcs =
  List.fold_left (fun g (a, b) -> add_arc g a b) empty arcs

let assert_list_set_equal expected actual =
  begin match List.minus expected actual with
    | [] -> ()
    | xs -> Alcotest.fail
        ("Expected but did not find: " ^
           (String.concat ", " (List.map Term.aty_to_string xs)))
  end ;
  begin match List.minus actual expected with
    | [] -> ()
    | xs -> Alcotest.fail
        ("Found but did not expect: " ^
           (String.concat ", " (List.map Term.aty_to_string xs)))
  end

let nd1 = Term.atybase "1"
let nd2 = Term.atybase "2"
let nd3 = Term.atybase "3"
let nd4 = Term.atybase "4"

let tests =
  suite "Graph" [
    test_case "Paths should be reflexive"
      (fun () ->
         let g = make_graph [] in
           Alcotest.check Alcotest.bool "expected true" true (is_path g nd1 nd1) ;
      );

    test_case "Empty graph should have no non-trivial paths"
      (fun () ->
         let g = make_graph [] in
           Alcotest.check Alcotest.bool "expected false" false (is_path g nd1 nd2) ;
      );

    test_case "Arcs should be one-way paths"
      (fun () ->
         let g = make_graph [(nd1, nd2)] in
           Alcotest.check Alcotest.bool "expected true" true (is_path g nd1 nd2) ;
           Alcotest.check Alcotest.bool "expected false" false (is_path g nd2 nd1) ;
      );

    test_case "Paths should be transitive"
      (fun () ->
         let g = make_graph [(nd1, nd2); (nd2, nd3)] in
           Alcotest.check Alcotest.bool "expected true" true (is_path g nd1 nd3) ;
      );

    test_case "Path transivitity should be propogated"
      (fun () ->
         let g = make_graph [(nd1, nd2); (nd3, nd4); (nd2, nd3)] in
           Alcotest.check Alcotest.bool "expected true" true (is_path g nd1 nd4) ;
      );

    test_case "Paths should avoid loops"
      (fun () ->
         let g = make_graph [(nd1, nd2); (nd2, nd1)] in
           Alcotest.check Alcotest.bool "expected false" false (is_path g nd1 nd3) ;
           Alcotest.check Alcotest.bool "expected false" false (is_path g nd3 nd1) ;
      );

    test_case "Predecessors should be reflexive"
      (fun () ->
         let g = make_graph [] in
           assert_list_set_equal [nd1] (predecessors g nd1) ;
      );

    test_case "Predecessors should be transitive"
      (fun () ->
         let g = make_graph [(nd1, nd2); (nd3, nd4)] in
         let g' = add_arc g nd2 nd3 in
           assert_list_set_equal [nd3; nd4] (predecessors g nd4) ;
           assert_list_set_equal [nd1; nd2; nd3; nd4] (predecessors g' nd4) ;
      );

    test_case "Predecessors should avoid loops"
      (fun () ->
         let g = make_graph [(nd1, nd2); (nd2, nd1)] in
           assert_list_set_equal [nd1; nd2] (predecessors g nd1) ;
           assert_list_set_equal [nd1; nd2] (predecessors g nd2) ;
      );
  ]
