let () =
  Alcotest.run "Abella"
    [
      Test_unify.tests ;
      Test_term.tests ;
      Test_context.tests ;
      Test_graph.tests ;
      Test_subordination.tests ;
      Test_metaterm.tests ;
      Test_typing.tests ;
      Test_parser.tests ;
      Test_tactics.tests ;
      (* TODO Test_prover.tests ; *)
      Test_web.tests ;
    ]
