(** Type expressions *)

module P : sig
  type t = Longident.t

  val pp : Format.formatter -> t -> unit
  val compare : t -> t -> int
end

(** The skeleton of type expressions,
    with parametrized variable and set. *)
type ('v, 's) skel =
  | Var of 'v
  | Constr of P.t * ('v, 's) skel array
  | Arrow of 's * ('v, 's) skel
  | Tuple of 's
  | Unknown of int
  | Unit

(** Non-normalized type expressions.

    The set of smart constructors normalize partially
    the structure.

    Use {!normalize} to get a normalized type expression.
*)
module Raw : sig

  type t = private (string, set) skel
  and set = S of t Sequence.t

  val arrow : t -> t -> t
  val tuple : t Sequence.t -> t
  val unknown : 'a -> t
  val constr : P.t -> t array -> t

  type varset
  val varset : unit -> varset

  val var : varset -> string -> t
end

module rec Nf : (Set.OrderedType with type t = (int, NSet.t) skel)
and NSet : Custom_set.S with type elt = Nf.t

type t = Nf.t
val compare : t -> t -> int
val equal : t -> t -> bool

module HC : Hashcons.S with type key = t

val normalize : ?ht:HC.t -> Raw.varset -> Raw.t -> t

val of_outcometree : ?ht:HC.t -> Outcometree.out_type -> t

val pp : Format.formatter -> t -> unit
