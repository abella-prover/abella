(* 
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2013  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See COPYING for licensing details.
 *)

if Array.length Sys.argv <> 3 then failwith "bad args" ;;

Sys.command (
  Printf.sprintf "mv %S %S"
    Sys.argv.(1)
    (Sys.argv.(2) ^ (if Sys.os_type <> "Unix" then ".exe" else ""))
) ;;
