(lang dune 3.20)
(name abella)
(version 2.1.0-dev)
(using menhir 2.0)

(generate_opam_files true)

(package
 (name abella)
 (synopsis "Interactive theorem prover based on lambda-tree syntax")
 (maintainers "kaustuv@chaudhuri.info")
 (authors
  "Andrew Gacek"
  "Yuting Wang"
  "Kaustuv Chaudhuri")
 (license "GPL-3.0-only")
 (homepage "https://abella-prover.org")
 (bug_reports "https://github.com/abella-prover/abella/issues")
 (source
  (github abella-prover/abella))
 (depends
  (ocaml
   (>= 4.12.0))
  (base64
   (>= 3.5.1))
  (cmdliner
   (>= 1.2.0))
  (menhir
   (>= 20211012))
  (re
   (>= 1.11.0))
  (yojson
   (>= 2.1.1))
  (ppxlib
   (>= 0.28.0))
  (ounit2 :with-test)))
