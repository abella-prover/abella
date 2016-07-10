open OUnit
open Test_helper
open Extensions
open Graph

let make_graph arcs =
  List.fold_left (fun g (a, b) -> add_arc g a b) empty arcs

let assert_list_set_equal expected actual =
  begin match List.minus expected actual with
    | [] -> ()
    | xs -> assert_failure
        ("Expected but did not find: " ^
           (String.concat ", " (List.map Term.aty_to_string xs)))
  end ;
  begin match List.minus actual expected with
    | [] -> ()
    | xs -> assert_failure
        ("Found but did not expect: " ^
           (String.concat ", " (List.map Term.aty_to_string xs)))
  end

let nd1 = Term.atybase "1"
let nd2 = Term.atybase "2"
let nd3 = Term.atybase "3"
let nd4 = Term.atybase "4"

let tests =
  "Graph" >::: [
    "Paths should be reflexive" >::
      (fun () ->
         let g = make_graph [] in
           assert_true (is_path g nd1 nd1) ;
      );

    "Empty graph should have no non-trivial paths" >::
      (fun () ->
         let g = make_graph [] in
           assert_false (is_path g nd1 nd2) ;
      );

    "Arcs should be one-way paths" >::
      (fun () ->
         let g = make_graph [(nd1, nd2)] in
           assert_true (is_path g nd1 nd2) ;
           assert_false (is_path g nd2 nd1) ;
      );

    "Paths should be transitive" >::
      (fun () ->
         let g = make_graph [(nd1, nd2); (nd2, nd3)] in
           assert_true (is_path g nd1 nd3) ;
      );

    "Path transivitity should be propogated" >::
      (fun () ->
         let g = make_graph [(nd1, nd2); (nd3, nd4); (nd2, nd3)] in
           assert_true (is_path g nd1 nd4) ;
      );

    "Paths should avoid loops" >::
      (fun () ->
         let g = make_graph [(nd1, nd2); (nd2, nd1)] in
           assert_false (is_path g nd1 nd3) ;
           assert_false (is_path g nd3 nd1) ;
      );

    "Predecessors should be reflexive" >::
      (fun () ->
         let g = make_graph [] in
           assert_list_set_equal [nd1] (predecessors g nd1) ;
      );

    "Predecessors should be transitive" >::
      (fun () ->
         let g = make_graph [(nd1, nd2); (nd3, nd4)] in
         let g' = add_arc g nd2 nd3 in
           assert_list_set_equal [nd3; nd4] (predecessors g nd4) ;
           assert_list_set_equal [nd1; nd2; nd3; nd4] (predecessors g' nd4) ;
      );

    "Predecessors should avoid loops" >::
      (fun () ->
         let g = make_graph [(nd1, nd2); (nd2, nd1)] in
           assert_list_set_equal [nd1; nd2] (predecessors g nd1) ;
           assert_list_set_equal [nd1; nd2] (predecessors g nd2) ;
      );
  ]
