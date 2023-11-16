(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* All output from Abella *)

open Extensions

open struct
  let last_id : int ref = ref (-1)
end

type message = {
  kind : string ;
  id : int ;
  fields : (string * Json.t) list ;
}


let message ?(fields = []) kind =
  incr last_id ;
  { kind ; id = !last_id ; fields }

let extend msg k v =
  { msg with fields = (k, v) :: msg.fields }

let commit msg : Json.t =
  `Assoc (("id", `Int msg.id) ::
          ("type", `String msg.kind) ::
          msg.fields)

type t =
  | Channel of out_channel
  | Buffer of { out : Buffer.t ; err : Buffer.t ; base : out_channel }
  | Json of { mutable out : Json.t list ; base : out_channel }
  | Null

let dest : t ref = ref @@ Channel Stdlib.stdout

let annotation_mode () =
  match !dest with
  | Channel base
  | Buffer { base ; _ } ->
      dest := Json { out = [] ; base }
  | Json _ | Null -> ()

type severity = Info | Error

let msg_printfk k ?(post = fun x -> x) ?(severity = Info) fmt =
  Printf.ksprintf begin fun str ->
    let str = post str in
    let doit () =
      match !dest with
      | Channel out ->
          Printf.fprintf out "%s\n%!" str
      | Buffer { out ; err ; _ } ->
          let buf = if severity = Info then out else err in
          Buffer.add_string buf str ;
          Buffer.add_string buf "\n"
      | Json js -> begin
          let msg = message "system_message" ~fields:[
              "severity", `String (match severity with
                  | Info -> "info"
                  | Error -> "error") ;
              "message", `String str
            ] in
          js.out <- commit msg :: js.out
        end
      | Null -> ()
    in
    doit () ; k str
  end fmt

let msg_printf ?post ?severity fmt =
  msg_printfk ignore ?post ?severity fmt

let msg_format ?post ?severity fmt =
  Format.kasprintf (msg_printf ?post ?severity "%s") fmt

module type TRACE = sig
  val printf : ?kind:string -> ('a, unit, string, unit) Stdlib.format4 -> 'a
  val format : ?kind:string -> ('a, Format.formatter, unit, unit) Stdlib.format4 -> 'a
end

open struct
  module Trace : TRACE = struct
    let kind_to_string = function
      | None -> ""
      | Some kind -> ":" ^ kind
    let str_prefix ?kind str =
      let prefix = "[TRACE" ^ kind_to_string kind ^ "] " in
      String.split_on_char '\n' str
      |> List.map (fun str -> prefix ^ str)
      |> String.concat "\n"
    let printf ?kind fmt = msg_printf ~post:(str_prefix ?kind) fmt
    let format ?kind fmt = msg_format ~post:(str_prefix ?kind) fmt
  end
end

let trace_verbosity = ref 0
let trace ?v fn =
  match v with
  | Some v when v >= !trace_verbosity -> ()
  | _ -> fn (module Trace : TRACE)

let link_message ~pos ~url =
  match !dest with
  | Json js ->
      let msg = message "link" ~fields:[
          "source", json_of_position pos ;
          "url", `String url
        ] in
      js.out <- commit msg :: js.out
  | _ -> ()

let non_annot fmt =
  Printf.ksprintf begin fun str ->
      match !dest with
      | Channel out ->
          output_string out str ;
          flush out
      | Buffer { out ; _ } ->
          Buffer.add_string out str
      | Json _ | Null -> ()
  end fmt

let non_annot_format fmt =
  Format.kasprintf (non_annot "%s") fmt

let json thing =
  match !dest with
  | Json js ->
      js.out <- thing :: js.out
  | _ -> ()

let commit_message msg = commit msg |> json

let blank_line () =
  match !dest with
  | Channel out ->
      output_string out "\n" ;
      flush out
  | Buffer { out ; _ } ->
      Buffer.add_string out "\n"
  | _ -> ()

let flush () =
  match !dest with
  | Channel out ->
      close_out out
  | Buffer { out ; err ; base } ->
      output_string base @@ Buffer.contents out ;
      output_string base "\n################################################################################\n" ;
      output_string base @@ Buffer.contents err ;
      close_out base
  | Json { out ; base } ->
      (* Json.pretty_to_channel base @@ `List (List.rev out) ; *)
      Json.to_channel base @@ `List (List.rev out) ;
      close_out base
  | Null -> ()

let exit code = flush () ; Stdlib.exit code
