open OUnit
open Test_helper

let eq a b = Term.eq (Norm.deep_norm a) (Norm.deep_norm b)

let assert_term_equal = assert_equal ~cmp:eq ~printer:Pprint.term_to_string

let assert_pprint_equal s t = assert_string_equal s (Pprint.term_to_string t)
