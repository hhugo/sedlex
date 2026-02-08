(* The package sedlex is released under the terms of an MIT-like license. *)
(* See the attached LICENSE file.                                         *)
(* Copyright 2005, 2013 by Alain Frisch and LexiFi.                       *)

type regexp

val chars : Sedlex_cset.t -> regexp
val seq : regexp -> regexp -> regexp
val alt : regexp -> regexp -> regexp
val rep : regexp -> regexp
val plus : regexp -> regexp
val eps : regexp
val compl : regexp -> regexp option

(* If the argument is a single [chars] regexp, returns a regexp
   which matches the complement set.  Otherwise returns [None]. *)
val subtract : regexp -> regexp -> regexp option

(* If each argument is a single [chars] regexp, returns a regexp
   which matches the set (arg1 - arg2).  Otherwise returns [None]. *)
val intersection : regexp -> regexp -> regexp option
(* If each argument is a single [chars] regexp, returns a regexp
   which matches the intersection set.  Otherwise returns [None]. *)

val bind : regexp -> regexp * int * int
val reset_tags : unit -> unit

type dfa_state = {
  trans : (Sedlex_cset.t * int * int list) array;
  finals : bool array;
}

type dfa = dfa_state array
type compiled = { dfa : dfa; init_tags : int list; num_tags : int }

val compile : regexp array -> compiled
val dfa_to_dot : dfa -> string
