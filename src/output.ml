(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* All output from Abella *)

open Extensions

type kind =
  | TopCommand | ProofCommand
  | SystemMessage
  | Link

let kind_to_string = function
  | TopCommand -> "top_command"
  | ProofCommand -> "proof_command"
  | SystemMessage -> "system_message"
  | Link -> "link"

type message = {
  kind : kind ;
  id : int ;
  mutable fields : (string * Json.t) list ;
}

let last_id : int ref = ref (-1)

let fresh kind =
  incr last_id ;
  { kind ; id = !last_id ; fields = [] }

let extend msg k v =
  msg.fields <- (k, v) :: msg.fields

let last_command_id : int option ref = ref None

let commit msg : Json.t =
  begin match msg.kind with
  | TopCommand | ProofCommand ->
      last_command_id := Some msg.id
  | _ -> () end ;
  `Assoc (("id", `Int msg.id) ::
          ("type", `String (kind_to_string msg.kind)) ::
          msg.fields)

type t =
  | Channel of out_channel
  | Buffer of { out : Buffer.t ; err : Buffer.t ; base : out_channel }
  | Json of { mutable out : Json.t list ; base : out_channel }
  | Null

let dest : t ref = ref @@ Channel stdout

let annotation_mode () =
  match !dest with
  | Channel base
  | Buffer { base ; _ } ->
      dest := Json { out = [] ; base }
  | Json _ | Null -> ()

type severity = Info | Error

let system_message ?(severity = Info) fmt =
  Printf.ksprintf begin fun str ->
    match !dest with
    | Channel out ->
        Printf.fprintf out "%s\n%!" str
    | Buffer { out ; err ; _ } ->
        let buf = if severity = Info then out else err in
        Buffer.add_string buf str ;
        Buffer.add_string buf "\n"
    | Json js -> begin
        let msg = fresh SystemMessage in
        begin match !last_command_id with
          | None -> ()
          | Some id -> extend msg "after" @@ `Int id
        end ;
        extend msg "severity" @@ begin
            match severity with
            | Info -> `String "info"
            | Error -> `String "error"
          end ;
        extend msg "message" @@ `String str ;
        js.out <- commit msg :: js.out
      end
    | Null -> ()
  end fmt

let system_message_format ?severity fmt =
  Format.kasprintf (system_message ?severity "%s") fmt

let link_message ~pos ~url =
  match !dest with
  | Json js ->
      let msg = fresh Link in
      begin match !last_command_id with
        | None -> ()
        | Some id -> extend msg "parent" @@ `Int id
      end ;
      extend msg "source" @@ json_of_position pos ;
      extend msg "url" @@ `String url ;
      js.out <- commit msg :: js.out
  | _ -> ()

let ordinary fmt =
  Printf.ksprintf begin fun str ->
      match !dest with
      | Channel out ->
          output_string out str ;
          flush out
      | Buffer { out ; _ } ->
          Buffer.add_string out str
      | Json _ | Null -> ()
  end fmt

let json thing =
  match !dest with
  | Json js ->
      js.out <- thing :: js.out
  | _ -> ()

let commit_message msg = commit msg |> json

let ordinary_format fmt =
  Format.kasprintf (ordinary "%s") fmt

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
      Json.pretty_to_channel base @@ `List (List.rev out) ;
      (* Json.to_channel base @@ `List (List.rev out) ; *)
      close_out base
  | Null -> ()

let exit code = flush () ; Stdlib.exit code
