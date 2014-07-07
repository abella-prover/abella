(**************************************************************************)
(*                                                                        *)
(*  PPrint                                                                *)
(*                                                                        *)
(*  Francois Pottier, INRIA Paris-Rocquencourt                            *)
(*  Nicolas Pouillard, IT University of Copenhagen                        *)
(*                                                                        *)
(*  Copyright 2007-2013 INRIA. All rights reserved. This file is          *)
(*  distributed under the terms of the CeCILL-C license, as described     *)
(*  in the file LICENSE.                                                  *)
(*                                                                        *)
(**************************************************************************)

(** A pretty-printing engine and a set of basic document combinators. *)

(** {1 Building documents} *)

(** Documents must be built in memory before they are rendered. This may seem
    costly, but it is a simple approach, and works well. *)

(** The following operations form a set of basic (low-level) combinators for
    building documents. On top of these combinators, higher-level combinators
    can be defined: see {!PPrintCombinators}. *)

(** This is the abstract type of documents. *)
type document

(** The following basic (low-level) combinators allow constructing documents. *)

(** [empty] is the empty document. *)
val empty: document

(** [char c] is a document that consists of the single character [c]. This
    character must not be a newline. *)
val char: char -> document

(** [string s] is a document that consists of the string [s]. This string must
    not contain a newline. *)
val string: string -> document

(** [substring s ofs len] is a document that consists of the portion of the
    string [s] delimited by the offset [ofs] and the length [len]. This
    portion must contain a newline. *)
val substring: string -> int -> int -> document

(** [fancystring s apparent_length] is a document that consists of the string
    [s]. This string must not contain a newline. The string may contain fancy
    characters: color escape characters, UTF-8 or multi-byte characters,
    etc. Thus, its apparent length (which measures how many columns the text
    will take up on screen) differs from its length in bytes. *)
val fancystring: string -> int -> document

(** [fancysubstring s ofs len apparent_length] is a document that consists of
    the portion of the string [s] delimited by the offset [ofs] and the length
    [len]. This portion must contain a newline. The string may contain fancy
    characters. *)
val fancysubstring : string -> int -> int -> int -> document

(** [utf8string s] is a document that consists of the UTF-8-encoded string [s].
    This string must not contain a newline. *)
val utf8string: string -> document

(** [hardline] is a forced newline document. This document forces all enclosing
    groups to be printed in non-flattening mode. In other words, any enclosing
    groups are dissolved. *)
val hardline: document

(** [blank n] is a document that consists of [n] blank characters. *)
val blank: int -> document

(** [break n] is a document which consists of either [n] blank characters,
    when forced to display on a single line, or a single newline character,
    otherwise. Note that there is no choice at this point: choices are encoded
    by the [group] combinator. *)
val break: int -> document

(** [doc1 ^^ doc2] is the concatenation of the documents [doc1] and [doc2]. *)
val (^^): document -> document -> document

(** [nest j doc] is the document [doc], in which the indentation level has
    been increased by [j], that is, in which [j] blanks have been inserted
    after every newline character. Read this again: indentation is inserted
    after every newline character. No indentation is inserted at the beginning
    of the document. *)
val nest: int -> document -> document

(** [group doc] encodes a choice. If possible, then the entire document [group
    doc] is rendered on a single line. Otherwise, the group is dissolved, and
    [doc] is rendered. There might be further groups within [doc], whose
    presence will lead to further choices being explored. *)
val group: document -> document

(** [column f] is the document obtained by applying the function [f] to the
    current column number. This combinator allows making the construction of
    a document dependent on the current column number. *)
val column: (int -> document) -> document

(** [nesting f] is the document obtained by applying the function [f] to the
    current indentation level, that is, the number of indentation (blank)
    characters that were inserted at the beginning of the current line. *)
val nesting: (int -> document) -> document

(** [position f] is the document obtained by applying the function [f]
    to the current position in the rendered output. The position
    consists of [bol], which is the character-offset of the beginnig
    of the current line (starting at 0), [line], which is the current
    line (starting at 1), and [column], which is the current column
    (starting at 0). The current character-offset is always given by
    [bol + column]. *)
val position : (bol:int -> line:int -> column:int -> document) -> document

(** [ifflat doc1 doc2] is rendered as [doc1] if part of a group that can be
    successfully flattened, and is rendered as [doc2] otherwise. Use this
    operation with caution. Because the pretty-printer is free to choose
    between [doc1] and [doc2], these documents should be semantically
    equivalent. *)
val ifflat: document -> document -> document

(** {1 Rendering documents} *)

(** This renderer sends its output into an output channel. *)
module ToChannel : PPrintRenderer.RENDERER
  with type channel = out_channel
   and type document = document

(** This renderer sends its output into a memory buffer. *)
module ToBuffer : PPrintRenderer.RENDERER
  with type channel = Buffer.t
   and type document = document

(** This renderer sends its output into a formatter channel. *)
module ToFormatter : PPrintRenderer.RENDERER
  with type channel = Format.formatter
   and type document = document
