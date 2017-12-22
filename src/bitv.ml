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

module Default = struct

  type t = int
  type storage = int

  let max_length = Sys.int_size - 1
  let check_len len =
    assert (len <= max_length)

  let zeros ~len = check_len len ; 0
  let ones ~len = check_len len ; (1 lsl len) - 1
  let (&&) = (land)
  let (||) = (lor)
  let not = lnot
  let singleton ~len i = check_len len ; assert (i <= len) ; 1 lsl i
  let add ~len x i = x && singleton ~len i
  let all_until ~len i = check_len len ; assert (i < len) ; (1 lsl (i+1) - 1)
  let is_empty n = (n = 0)

  (* let pp = Format.pp_print_int *)
  let storage x = x
end
