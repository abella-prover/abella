open OUnit
open Lppterm

let tests =
  "LPP Term" >:::
    [
      "Printing" >:::
        [
          "foo" >::
            (fun () -> assert_equal 1 1);

          "bar" >::
            (fun () -> assert_equal 2 2);
          
(*          "{eval P V}" >::
            (fun () ->
               let t = 1 in
               let s = string_of_term t in
                 assert_equal "{eval P V}" s) ; *)
        ]
    ]
                 
