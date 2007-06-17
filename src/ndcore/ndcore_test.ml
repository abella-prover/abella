open OUnit
open Test_helper

let eq a b = Term.eq (Term.deep_norm a) (Term.deep_norm b)

let assert_term_equal = assert_equal ~cmp:eq ~printer:Term.term_to_string

let assert_pprint_equal s t = assert_string_equal s (Term.term_to_string t)
