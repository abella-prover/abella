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
           (String.concat ", " (List.map string_of_int xs)))
  end ;
  begin match List.minus actual expected with
    | [] -> ()
    | xs -> assert_failure
        ("Found but did not expect: " ^
           (String.concat ", " (List.map string_of_int xs)))
  end

let tests =
  "Graph" >::: [
    "Paths should be reflexive" >::
      (fun () ->
         let g = make_graph [] in
           assert_true (is_path g 1 1) ;
      );

    "Empty graph should have no non-trivial paths" >::
      (fun () ->
         let g = make_graph [] in
           assert_false (is_path g 1 2) ;
      );

    "Arcs should be one-way paths" >::
      (fun () ->
         let g = make_graph [(1, 2)] in
           assert_true (is_path g 1 2) ;
           assert_false (is_path g 2 1) ;
      );

    "Paths should be transitive" >::
      (fun () ->
         let g = make_graph [(1, 2); (2, 3)] in
           assert_true (is_path g 1 3) ;
      );

    "Path transivitity should be propogated" >::
      (fun () ->
         let g = make_graph [(1, 2); (3, 4); (2, 3)] in
           assert_true (is_path g 1 4) ;
      );

    "Paths should avoid loops" >::
      (fun () ->
         let g = make_graph [(1, 2); (2, 1)] in
           assert_false (is_path g 1 3) ;
           assert_false (is_path g 3 1) ;
      );

    "Predecessors should be reflexive" >::
      (fun () ->
         let g = make_graph [] in
           assert_list_set_equal [1] (predecessors g 1) ;
      );

    "Predecessors should be transitive" >::
      (fun () ->
         let g = make_graph [(1, 2); (3, 4)] in
         let g' = add_arc g 2 3 in
           assert_list_set_equal [3; 4] (predecessors g 4) ;
           assert_list_set_equal [1; 2; 3; 4] (predecessors g' 4) ;
      );

    "Predecessors should avoid loops" >::
      (fun () ->
         let g = make_graph [(1, 2); (2, 1)] in
           assert_list_set_equal [1; 2] (predecessors g 1) ;
           assert_list_set_equal [1; 2] (predecessors g 2) ;
      );
  ]
