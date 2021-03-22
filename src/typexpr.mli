(** Type expressions *)

(** Path *)
module P : sig
  type t = Longident.t

  val pp : Format.formatter -> t -> unit
  val compare : t -> t -> int
  val unit : t

  module Map : CCTrie.S with type key = t
  module HMap : CCHashtbl.S with type key = t
end

(** The skeleton of type expressions,
    with parametrized variable and set. *)
type ('var, 'tuple) skel =
  | Var of 'var
  | Constr of P.t * ('var, 'tuple) skel array
  | Tuple of 'tuple
  | Unknown of int
  | Unit
  | Arrow of 'tuple * ('var, 'tuple) skel

(** Non-normalized type expressions.

    The set of smart constructors normalize partially
    the structure.

    Use {!normalize} to get a normalized type expression.
*)
module Raw : sig

  type t = private (string option, set) skel
  and set = S of t list

  val arrow : t -> t -> t
  val tuple : t list -> t
  val unknown : 'a -> t
  val constr : P.t -> t array -> t

  val var : string option -> t
end

(** Normal form *)
module rec Nf : (Set.OrderedType with type t = (Variables.t, NSet.t) skel)
and NSet : sig
  include Custom_set.S with type elt = Nf.t
  val as_array : t -> elt array
end

type t = Nf.t
val compare : t -> t -> int
val equal : t -> t -> bool

module Hashcons : sig
  type elt = private {
    node: t;
    mutable id: int;
  }
  type t

  val create : int -> t
  val hashcons : t -> Nf.t -> elt
end

val normalize :
  gen:Variables.gen ->
  ht:Hashcons.t ->
  nametbl:label Variables.HMap.t ->
  Raw.t -> t

val vars : Nf.t -> Variables.t Iter.t

module Head : sig
  type t =
    | Var
    | Constr of P.t
    | Tuple
    | Other
    | Unit

  val get : Nf.t -> t
end

val pp : string Variables.HMap.t -> t Fmt.t
val pp_raw : Raw.t Fmt.t
