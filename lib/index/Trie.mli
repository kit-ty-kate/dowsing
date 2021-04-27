module type NODE = sig

  type key
  type 'v t

  val key : Type.t -> key

  val empty : 'v t
  val singleton : key -> 'v -> 'v t
  val add : key -> 'v -> 'v t -> 'v t
  val iter : 'v t -> (Type.t * 'v list) Iter.t
  val iter_with : key -> 'v t -> (Type.t * 'v list) Iter.t

end

module Leaf : NODE
module Node (Feat : Feature.S) (Sub : NODE) : NODE

module Make (Node : NODE) : sig

  type 'v t

  val empty : 'v t
  val add : Type.t -> 'v -> 'v t -> 'v t
  val iter : 'v t -> (Type.t * 'v list) Iter.t
  val iter_with : Type.t -> 'v t -> (Type.t * 'v list) Iter.t

end
