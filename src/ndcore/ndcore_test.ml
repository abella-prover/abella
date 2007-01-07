open OUnit

let eq a b = Term.eq (Norm.deep_norm a) (Norm.deep_norm b)

let assert_term_equal = assert_equal ~cmp:eq ~printer:Pprint.term_to_string
