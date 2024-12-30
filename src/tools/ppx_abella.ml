(*
 * Author: Kaustuv Chaudhuri <kaustuv@chaudhuri.info>
 * Copyright (C) 2024  Inria
 * See LICENSE for licensing details.
 *)

let do_tracing = true

open Ppxlib

let eposition ~loc =
  let open Ast_builder.Default in
  let start = loc.loc_start in
  pexp_record ~loc [
    (Located.lident ~loc "pos_fname", estring ~loc start.pos_fname) ;
    (Located.lident ~loc "pos_lnum", eint ~loc start.pos_lnum) ;
    (Located.lident ~loc "pos_cnum", eint ~loc start.pos_cnum) ;
    (Located.lident ~loc "pos_bol", eint ~loc start.pos_bol) ;
  ] None

let trace_expander =
  let name = "trace" in
  let context = Extension.Context.expression in
  let extractor = Ast_pattern.(single_expr_payload (pexp_apply (eint __) (many (no_label __)))) in
  let open Ast_builder.Default in
  let expand ~ctxt verb args =
    let loc = Expansion_context.Extension.extension_point_loc ctxt in
    if not do_tracing then eunit ~loc else
    match args with
    | fmt :: args ->
        let ( ^^ ) f1 f2 = eapply ~loc (evar ~loc "Stdlib.^^") [f1 ; f2] in
        let fmt =
          estring ~loc ("@[<v4>>>> [at %a]@,@[<b0>")
          ^^ fmt ^^
          estring ~loc "@]@]" in
        let pos_args =
          [ evar ~loc "Ppx_abella_lib.pp_location" ;
            eposition ~loc ] in
        eapply ~loc (evar ~loc "Ppx_abella_lib.format")
          (eint ~loc verb :: fmt :: pos_args @ args)
    | _ ->
        pexp_extension ~loc
          (Location.error_extensionf ~loc "Missing format string")
  in
  Extension.V3.declare name context extractor expand |>
  Context_free.Rule.extension

let bug_expander =
  let name = "bug" in
  let context = Extension.Context.expression in
  let extractor = Ast_pattern.(pstr nil) in
  let expand ~ctxt =
    let loc = Expansion_context.Extension.extension_point_loc ctxt in
    let open Ast_builder.Default in
    let erf = evar ~loc "Stdlib.Format.err_formatter" in
    let continuation =
      let reportme =
        eapply ~loc (evar ~loc "Stdlib.Format.fprintf")
          [ erf ;
            estring ~loc "@.Please report this at \
                         \ https://github.com/abella-prover/abella/issues@." ] in
      let fail =
        eapply ~loc (evar ~loc "Stdlib.failwith")
          [ estring ~loc "Bug" ] in
      pexp_fun ~loc Nolabel None (ppat_any ~loc)
        (esequence ~loc [ reportme ; fail ])
    in
    esequence ~loc
      [ eapply ~loc (evar ~loc "Stdlib.Format.fprintf")
          [ erf ;
            estring ~loc ("ABELLA BUG at %a@.") ;
            evar ~loc "Ppx_abella_lib.pp_location" ;
            eposition ~loc ] ;
        eapply ~loc (evar ~loc "Stdlib.Format.kfprintf")
          [ continuation ; erf  ] ]
  in
  Extension.V3.declare name context extractor expand |>
  Context_free.Rule.extension

let () =
  Driver.V2.register_transformation "ppx_abella"
    ~rules:[
      trace_expander ;
      (* tracef_expander ; *)
      bug_expander ;
    ]
