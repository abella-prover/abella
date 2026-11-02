(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026 Inria (Institut National de Recherche
 *                            en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

module M = Abella_doc_manifest

let test_relative_path () =
  let check = Alcotest.(check string) in
  check "same directory" "b.thm"
    (M.relative_path ~from:"a" ~target:"a/b.thm") ;
  check "nested target" "d/e.thm"
    (M.relative_path ~from:"a/b" ~target:"a/b/d/e.thm") ;
  check "sibling directory" "../b/c.thm"
    (M.relative_path ~from:"a/x" ~target:"a/b/c.thm") ;
  check "parent components" "../c.thm"
    (M.relative_path ~from:"a/b" ~target:"a/b/../c.thm") ;
  check "leading dot" "b.thm"
    (M.relative_path ~from:"./a" ~target:"./a/b.thm")

let () =
  Alcotest.run "doc_manifest" [
    "manifest", [
      Alcotest.test_case "relative paths" `Quick test_relative_path ;
    ] ;
  ]
