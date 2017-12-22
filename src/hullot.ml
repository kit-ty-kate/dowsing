
module type S = sig
  type bitset
  val iter : len:int -> small:(bitset -> bool) -> large:(bitset -> bool) -> bitset Sequence.t
end


module Make (B : Bitv.S) = struct

  type bitset = B.t

  type test = SmallEnough | LargeEnough

  let left_son_ge len h bv =
    B.(bv && not (singleton ~len h))

  let right_son_ge len h bv =
    B.(bv && not (all_until ~len (h - 1)))

  let left_son_se len h bv =
    B.(bv || all_until ~len (h - 1))

  let right_son_se len h bv =
    B.(bv || singleton ~len h)

  let rec iter_aux ~len ~large ~small height dir node k =
    match height, dir with
    | 0, LargeEnough ->
	    if large node then k node else ()

    | 0, SmallEnough ->
	    if small node then k node else ()

    | h, LargeEnough ->
	    if large node then
	      let () = (* left *)
 	        iter_aux
             ~len ~large ~small
            (h - 1) LargeEnough (left_son_ge len (pred h) node) k
        and () = (* right *)
	        iter_aux
             ~len ~large ~small
	          (h - 1) SmallEnough (right_son_ge len (pred h) node) k
        in
        ()
	    else ()
    | h, SmallEnough ->
	    if small node then
	      let () = (* left *)
 	        iter_aux
             ~len ~large ~small
	          (h - 1) LargeEnough (left_son_se len (pred h) node) k
	      and () =
	        iter_aux
             ~len ~large ~small
	          (h - 1) SmallEnough (right_son_se len (pred h) node) k
        in
        ()
	    else ()

  let iter ~len ~small ~large k =
    let root = B.ones ~len in
    iter_aux ~len ~large ~small len LargeEnough root k

end

module Default = Make (Bitv.Default)
