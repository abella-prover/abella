(***********************************************************************)
(* The OUnit library                                                   *)
(*                                                                     *)
(* Copyright (C) 2002, 2003, 2004, 2005 Maas-Maarten Zeeman.           *)
(* All rights reserved. See LICENCE for details.                       *)
(***********************************************************************)

let bracket set_up f tear_down () =
  let fixture = set_up () in
    try
      f fixture;
      tear_down fixture
    with
	e ->
	  tear_down fixture;
	  raise e

let assert_failure msg =
  failwith ("OUnit: " ^ msg)

let assert_bool msg b =
  if not b then assert_failure msg

let assert_string str =
  if not (str = "") then assert_failure str

let assert_equal ?(cmp = ( = )) ?printer ?msg expected actual  =
  let get_error_string _ =
    match printer, msg with
	None, None -> "not equal"
      | None, Some s -> (Format.sprintf "%s\nnot equal" s)
      | Some p, None -> (Format.sprintf "expected: %s but got: %s"
			   (p expected) (p actual))
      | Some p, Some s -> (Format.sprintf "%s\nexpected: %s but got: %s"
			     s (p expected) (p actual))
  in
    if not (cmp expected actual) then
      assert_failure (get_error_string ())

let raises f =
  try
    f ();
    None
  with
      e -> Some e

let assert_raises ?msg exn (f: unit -> 'a) =
  let pexn = Printexc.to_string in
  let get_error_string _ =
    let str = Format.sprintf
      "expected exception %s, but no exception was not raised." (pexn exn)
    in
      match msg with
	  None -> assert_failure str
	| Some s -> assert_failure (Format.sprintf "%s\n%s" s str)
  in
    match raises f with
	None -> assert_failure (get_error_string ())
      | Some e -> assert_equal ?msg ~printer:pexn exn e

(* Compare floats up to a given relative error *)
let cmp_float ?(epsilon = 0.00001) a b =
  abs_float (a -. b) <= epsilon *. (abs_float a) ||
    abs_float (a -. b) <= epsilon *. (abs_float b)

(* Now some handy shorthands *)
let (@?) = assert_bool

(* The type of tests *)
type test =
    TestCase of (unit -> unit)
  | TestList of test list
  | TestLabel of string * test

(* Some shorthands which allows easy test construction *)
let (>:) s t = TestLabel(s, t)             (* infix *)
let (>::) s f = TestLabel(s, TestCase(f))  (* infix *)
let (>:::) s l = TestLabel(s, TestList(l)) (* infix *)

(* Return the number of available tests *)
let rec test_case_count test =
  match test with
      TestCase _ -> 1
    | TestLabel (_, t) -> test_case_count t
    | TestList l -> List.fold_left (fun c t -> c + test_case_count t) 0 l

type node = ListItem of int | Label of string
type path = node list

let string_of_node node =
  match node with
      ListItem n -> (string_of_int n)
    | Label s -> s

let string_of_path path =
  List.fold_left
    (fun a l ->
       if a = "" then
	 l
       else
	 l ^ ":" ^ a) "" (List.map string_of_node path)

(* Some helper function, they are generally applicable *)
(* Applies function f in turn to each element in list. Function f takes
   one element, and integer indicating its location in the list *)
let mapi f l =
  let rec rmapi cnt l =
    match l with
	[] -> []
      | h::t -> (f h cnt)::(rmapi (cnt + 1) t)
  in
    rmapi 0 l

let fold_lefti f accu l =
  let rec rfold_lefti cnt accup l =
    match l with
	[] -> accup
      | h::t -> rfold_lefti (cnt + 1) (f accup h cnt) t
  in
    rfold_lefti 0 accu l

(* Returns all possible paths in the test. The order is from test case
   to root
*)
let test_case_paths test =
  let rec tcps path test =
    match test with
	TestCase _ -> [path]
      | TestList tests ->
	  List.concat (mapi (fun t i -> tcps ((ListItem i)::path) t) tests)
      | TestLabel (l, t) -> tcps ((Label l)::path) t
  in
    tcps [] test

(* The possible test results *)
type test_result =
    RSuccess of path
  | RFailure of path * string
  | RError of path * string

let is_success = function
    RSuccess _ -> true
  | RError _ -> false
  | RFailure _ -> false

let is_failure = function
    RFailure _ -> true
  | RError _ -> false
  | RSuccess _ -> false

let is_error = function
    RError _ -> true
  | RFailure _ -> false
  | RSuccess _ -> false

let result_flavour = function
    RError _ -> "Error"
  | RFailure _ -> "Failure"
  | RSuccess _ -> "Success"

let result_path = function
    RSuccess path -> path
  | RError (path, _) -> path
  | RFailure (path, _) -> path

let result_msg = function
    RSuccess _ -> "Success"
  | RError (_, msg) -> msg
  | RFailure (_, msg) -> msg

(* Returns true if the result list contains successes only *)
let rec was_successful results =
  match results with
      [] -> true
    | RSuccess _::t -> was_successful t
    | RFailure _::_ -> false
    | RError _::_ -> false

(* Events which can happen during testing *)
type test_event =
    EStart of path
  | EEnd of path
  | EResult of test_result

(* Run all tests, report starts, errors, failures, and return the results *)
let perform_test report test =
  let run_test_case f path =
    try
      f ();
      RSuccess path
    with
	Failure s -> RFailure (path, s)
      | s -> RError (path, (Printexc.to_string s))
  in
  let rec run_test path results test =
    match test with
	TestCase(f) ->
	  report (EStart path);
	  let result = run_test_case f path in
	    report (EResult result);
	    report (EEnd path);
	    result::results
      | TestList (tests) ->
	  fold_lefti
	    (fun results t cnt -> run_test ((ListItem cnt)::path) results t)
	    results tests
      | TestLabel (label, t) ->
	  run_test ((Label label)::path) results t
  in
    run_test [] [] test

(* Function which runs the given function and returns the running time
   of the function, and the original result in a tuple *)
let time_fun f x y =
  let begin_time = Unix.gettimeofday () in
    (Unix.gettimeofday () -. begin_time, f x y)

(* A simple (currently too simple) text based test runner *)
let run_test_tt ?(verbose=false) test =
  let printf = Format.printf in
  let separator1 =
    "======================================================================" in
  let separator2 =
    "----------------------------------------------------------------------" in
  let string_of_result = function
      RSuccess _ ->
	if verbose then "ok\n" else "."
    | RFailure (_, _) ->
	if verbose then "FAIL\n" else "F"
    | RError (_, _) ->
	if verbose then "ERROR\n" else "E"
  in
  let report_event = function
      EStart p ->
	if verbose then printf "%s ... " (string_of_path p)
    | EEnd _ -> ()
    | EResult result ->
	printf "%s@?" (string_of_result result);
  in
  let print_result_list results =
      List.iter
	(fun result -> printf "%s\n%s: %s\n\n%s\n%s\n"
	   separator1
	   (result_flavour result)
	   (string_of_path (result_path result))
	   (result_msg result)
	   separator2)
	results
  in

  (* Now start the test *)
  let running_time, results = time_fun perform_test report_event test in
  let errors = List.filter is_error results in
  let failures = List.filter is_failure results in

    if not verbose then printf "\n";

    (* Print test report *)
    print_result_list errors;
    print_result_list failures;
    printf "Ran: %d tests in: %.2f seconds.\n"
      (List.length results) running_time;

    (* Print final verdict *)
    if was_successful results then
      printf "OK\n"
    else
      printf "FAILED: Cases: %d Tried: %d Errors: %d Failures: %d\n"
	(test_case_count test) (List.length results)
	(List.length errors) (List.length failures);

    (* Return the results possibly for further processing *)
    results

(* Call this one from you test suites *)
let run_test_tt_main suite =
  let verbose = ref false in
  let set_verbose _ = verbose := true in

    Arg.parse
      [("-verbose", Arg.Unit set_verbose, "Run the test in verbose mode.");]
      (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
      ("usage: " ^ Sys.argv.(0) ^ " [-verbose]");

    let result = run_test_tt ~verbose:!verbose suite in
      if not (was_successful result) then
	exit 1
      else
	result
