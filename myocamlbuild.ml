open Ocamlbuild_plugin ;;

let ocamlc_opts     = ["-g" ; "-annot" ; "-warn-error" ; "A"]
let ocamlopt_opts   = ["-g" ; "-annot" ; "-nodynlink" ; "-warn-error" ; "A"]
let ocamldep_opts   = []
let ocamldoc_opts   = []
let ocamlmktop_opts = []

let sas ss = S (List.map (fun s -> A s) ss)

let _ = dispatch begin function
   | After_rules ->
       flag ["ocaml" ; "compile"] (A "-annot") ;
       flag ["ocaml" ; "compile"] (S [A "-warn-error" ; A "A"]) ;
       flag ["ocaml" ; "native" ; "compile"] (A "-nodynlink") ;
       flag ["ocaml" ; "link" ; "program"] (A "-linkpkg") ;
   | _ -> ()
end
