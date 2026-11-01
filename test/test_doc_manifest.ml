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

let test_site_manifest_url () =
  let check = Alcotest.(check (option string)) in
  check "relative path" (Some "/examples/a/foo.project.json")
    (M.site_manifest_url "examples/a/foo") ;
  check "normalized path" (Some "/examples/a/foo.project.json")
    (M.site_manifest_url "./examples//a/foo") ;
  check "absolute path" None (M.site_manifest_url "/tmp/foo") ;
  check "outside the site root" None (M.site_manifest_url "../foo")

let test_url_encode () =
  Alcotest.(check string) "reserved characters" "%2Fa%20b%2Bc"
    (M.url_encode "/a b+c")

let test_manifest_json () =
  let json = M.manifest_json ~entry:"a.thm" ~files:["a.thm"; "b.sig"] in
  Alcotest.(check string) "version 2 document"
    {|{"version":2,"entry":"a.thm","files":["a.thm","b.sig"]}|}
    (Yojson.Safe.to_string json)

let () =
  Alcotest.run "doc_manifest" [
    "manifest", [
      Alcotest.test_case "relative paths" `Quick test_relative_path ;
      Alcotest.test_case "site URLs" `Quick test_site_manifest_url ;
      Alcotest.test_case "URL encoding" `Quick test_url_encode ;
      Alcotest.test_case "JSON document" `Quick test_manifest_json ;
    ] ;
  ]
