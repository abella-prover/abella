open Abella_lib
open Abella_types
open Term
open Test_helper

let def_of pred clauses =
  { flavor = Inductive ;
    typarams = [] ;
    mutual = Itab.singleton pred propty ;
    clauses }

let contains haystack needle =
  let n = String.length needle and h = String.length haystack in
  let rec spin i =
    i + n <= h &&
    (String.sub haystack i n = needle || spin (i + 1))
  in
  spin 0

let assert_strat_failure def is_defined =
  try
    Checks.check_def ~errors:true ~def ~is_defined () ;
    Alcotest.fail "Expected a stratification failure"
  with
  | Failure msg ->
      Alcotest.check Alcotest.bool "wrong failure" true
        (contains msg "might not be stratified")

let assert_warning def is_defined =
  let dest = !Output.dest in
  Output.collect_mode () ;
  Fun.protect ~finally:(fun () -> Output.dest := dest) begin fun () ->
    Checks.check_def ~errors:false ~def ~is_defined () ;
    let messages =
      Output.drain () |> List.filter_map begin function
        | `Assoc fields -> begin
            match List.assoc_opt "message" fields with
            | Some (`String msg) -> Some msg
            | _ -> None
          end
        | _ -> None
      end
    in
      Alcotest.check Alcotest.bool "warning missing" true
        (List.exists (fun msg -> contains msg "might not be stratified")
           messages)
  end

let tests =
  suite "Checks" [
      test_case "Declared higher-order argument is potentially negative"
        (fun () ->
           let def =
             def_of "russell_d"
               (parse_defs "russell_d := ho_decl (x \\ russell_d).")
           in
           let is_defined id = id = "russell_d" in
             assert_warning def is_defined ;
             assert_strat_failure def is_defined
        );

      test_case "Defined higher-order argument is accepted"
        (fun () ->
           let def =
             def_of "russell_d"
               (parse_defs "russell_d := ho_decl (x \\ russell_d).")
           in
           let is_defined id = List.mem id ["russell_d" ; "ho_decl"] in
             Checks.check_def ~errors:true ~def ~is_defined ()
        );

      test_case "Direct negative occurrence still fails"
        (fun () ->
           let def =
             def_of "russell_d"
               (parse_defs
                  "russell_d := russell_d -> russell_d.")
           in
           let is_defined id = id = "russell_d" in
             assert_strat_failure def is_defined
        );
    ]
