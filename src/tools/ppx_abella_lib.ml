(*
 * Author: Kaustuv Chaudhuri <kaustuv@chaudhuri.info>
 * Copyright (C) 2024  Inria
 * See LICENSE for licensing details.
 *)

(** Small library for ppx_abella *)

module type PRINTER = sig
  val format : ('a, Stdlib.Format.formatter, unit) Stdlib.format -> 'a
end

let printer : (module PRINTER) ref =
  let module Default = struct
    let format = Stdlib.Format.eprintf
  end in
  ref (module Default : PRINTER)

let verbosity : int ref = ref 0

let format v fmt =
  if v > !verbosity then Stdlib.Format.(ifprintf err_formatter fmt) else
  let (module Printer) = !printer in
  Printer.format fmt

let pp_location out (loc : Stdlib.Lexing.position) =
  Stdlib.Format.fprintf out
    "%s:%d.%d"
    loc.pos_fname
    loc.pos_lnum
    (loc.pos_cnum - loc.pos_bol)
