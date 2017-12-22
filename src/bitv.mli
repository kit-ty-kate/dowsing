module type S = sig
  type storage
  type t = private storage
  val zeros : len:int ->  t
  val ones  : len:int ->  t
  val (&&) : t -> t -> t
  val (||) : t -> t -> t
  val not : t -> t
  val add : len:int -> t -> int -> t
  val singleton : len:int -> int -> t
  val all_until : len:int -> int -> t
  val is_empty : t -> bool
  (* val pp : len:int -> Format.formatter -> t -> unit *)

  val storage : t -> storage

  val max_length : int
end

module Default : S with type storage = int
