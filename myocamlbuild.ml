open Ocamlbuild_plugin ;;

let _ = dispatch begin function
   | After_rules ->
       flag ["ocaml" ; "compile"] (A "-annot") ;
       flag ["ocaml" ; "compile"] (S [A "-w" ; A "@3@5@6@8..12@14@20@26@28@29"]) ;
       flag ["ocaml" ; "native" ; "compile"] (A "-nodynlink") ;
   | _ -> ()
end
