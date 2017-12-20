(**************************************************************************)
(*                                                                        *)
(*     The CiME3 tool box for term rewriting                              *)
(*     Copyright (C) 2007                                                 *)
(*                                                                        *)
(*                                                                        *)
(*     Evelyne Contejean                                                  *)
(*     Pierre Courtieu                                                    *)
(*     Julien Forest                                                      *)
(*     Olivier Pons                                                       *)
(*     Xavier Urbain                                                      *)
(*                                                                        *)
(*     CNRS-LRI-Universite Paris Sud XI                                   *)
(*     Cedric-CNAM-ENSIIE                                                 *)
(*                                                                        *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(***************************************************************************
   Bit fields encode vectors of bits of arbitrary length.
   Boolean operations are provided : body.

   $Id: bit_field.ml 4 2004-10-19 14:04:20Z contejea $

 ***************************************************************************)
open Format

module type S =
sig
  type t
  val all_zero : int ->  t
  val all_one  : int ->  t
  val bit_length : t -> int
  val bit_and : t -> t -> t
  val bit_or : t -> t -> t
  val bit_not : t -> t
  val bit_nth : int -> int -> t
  val bit_nth_first : int -> int -> t
  val is_zero : t -> bool
  val atmost_one_one : t -> bool
  val bit_field_to_vect_of_bits : int -> t -> int array
  val vect_of_bits_to_bit_field : int array -> t
  val print_bit_field : formatter -> int -> t -> unit
end

(* For vectors of bits of length < 32 *)

module Small =
struct
  type t = int
  let all_zero _ = 0
  let all_one n = pred (1 lsl n)
  let bit_length _ = 1
  let bit_and = (land)
  let bit_or = (lor)
  let bit_not = lnot
  let bit_nth n _ = 1 lsl n
  let bit_nth_first n _ = pred (1 lsl (succ n))
  let is_zero n = (n = 0)
  let atmost_one_one n = (n land (pred n)) = 0
  let bit_field_to_vect_of_bits len n =
    let v = Array.make len 0
    and n' = ref n in
	  for i = 0 to pred len do
	    if (!n' land 1) = 1
	    then v.(i) <- 1;
	    n' := (!n' lsr 1)
	  done;
	  v
  let vect_of_bits_to_bit_field u =
    let l = Array.length u in
	  if l >= 32
	  then assert false
	  else
	    let n = ref 0 in
	    for j=0 to pred l do
	      if u.(j) > 0
	      then n:= !n + (1 lsl j)
	    done;
	    !n
  let print_bit_field fmt l n =
    let v = bit_field_to_vect_of_bits l n in
	  fprintf fmt "[|";
	  for i=0 to (l - 2) do
	    fprintf fmt "%d ;" v.(i)
	  done;
	  fprintf fmt "%d|]" v.(pred l)
end

(*
  For vectors of bits of arbitrary length
*)

module Large =
struct
  type t = int array

  (* [all_zero l] returns a bit field of [l] 0s. *)
  let all_zero l =
    let q = if (l mod 31) = 0 then (l / 31) else succ (l / 31) in
	  Array.make q 0

  (* [all_one l] returns a bit field of [l] 1s. *)
  let all_one l =
    let q = l / 31
    and r = l mod 31 in
	  if r = 0
	  then Array.make q (lnot 0)
	  else
	    let v = Array.make (succ q) (lnot 0) in
      v.(q) <- pred (1 lsl r);
      v

  let bit_length bf = Array.length bf

  (* [bit_and] is a bit wise "and", and fails when the bit_fields encode
     vectors of bit of different length. *)
  let bit_and bf1 bf2 =
    try
	    let d = Array.length bf1 in
	    let v = Array.make d 0 in
      for i=0 to (pred d) do
        v.(i) <- bf1.(i) land bf2.(i)
      done;
      v
    with Failure _ -> assert false

  (* [bit_or] is a bit wise "or", and fails when the bit_fields encode
     vectors of bit of different length. *)
  let bit_or bf1 bf2 =
    try
	    let d = Array.length bf1 in
	    let v = Array.make d 0 in
      for i=0 to (pred d) do
        v.(i) <- bf1.(i) lor bf2.(i)
      done;
      v
    with Failure _ -> assert false

  (* [bit_not] is a bit wise "not" *)
  let bit_not bf =
    let d = Array.length bf in
    let v = Array.make d 0 in
	  for i=0 to (pred d) do
	    v.(i) <- lnot bf.(i)
	  done;
	  v

  (* [bit_nth n l] returns a [bit_field] encoding a vector of bits of
	   length l where all the bits are equal to 0, except at position
	   [n] which is a 1.
	   \begin{verbatim}
                       (0,...,0,1,0,...,0)
                        ^       ^       ^
                        |       |       |
                        0       n    (31*l) -1
	     \end{verbatim} *)
  let bit_nth n l =
    try
	    let qn = n / 31
	    and rn = n mod 31 in
	    let v = Array.make l 0 in
	    v.(qn) <- 1 lsl rn;
	    v
    with Failure _ -> assert false


  (* [bit_nth_first n l] returs a [bit_field] encoding a vector of bits of
	   length 31*l where the first nth bits are equal to 1, the others
	   being equal to 0.
	   \begin{verbatim}
                       (1,...,1,1,0,...,0)
                        ^       ^       ^
                        |       |       |
                        0       n    (31*l) -1
	     \end{verbatim} *)
  let bit_nth_first n' l =
    let n = succ n' in
	  try
	    let qn = n / 31
	    and rn = n mod 31 in
	    let v = Array.make l 0 in
	    if rn = 0
	    then Array.blit (Array.make qn (lnot 0)) 0 v 0 qn
	    else
	      begin
		      Array.blit (Array.make (succ qn) (lnot 0)) 0 v 0 (succ qn);
		      v.(qn) <- pred (1 lsl rn)
	      end;
	    v
	  with Failure _ -> assert false

  (* [is_zero b] returns [true] if the bit field [b] encodes the integer
     0 in base 2. *)
  let is_zero bf =
    try
	    for i=0 to (pred (Array.length bf)) do
        if (bf.(i) <> 0)
        then raise Exit
	    done;
	    true
    with Exit -> false

  (* [atmost_one_one b] returns [true] if the bit field [b] encodes a
	   power of 2 in base 2. *)
  let atmost_one_one bf =
    try
	    let l = Array.length bf
	    and state = ref 0 in
	    for i=0 to (pred l) do
        let p = bf.(i) in
        if p <> 0
        then
		      begin
		        if (!state <> 0)
		        then raise Exit
		        else
		          begin
                if (p land (pred p)) = 0
                then state := 1
                else raise Exit
              end
		      end
	    done;
	    true
    with Exit -> false


  (* [int_to_vect_of_bits length n] returns the vector of bits of length
     [length] encoding the representation of [n] in base 2. *)
  let int_to_vect_of_bits len n =
    let v = Array.make len 0
    and n' = ref n in
	  for i = 0 to (pred len) do
	    if (!n' land 1) = 1
	    then v.(i) <- 1;
	    n' := (!n' lsr 1)
	  done;
	  v

  (* [bit_field_to_vect_of_bits l bf] returns the vector of bits
     of length [l] encoded by the [bit_field] [bf]. *)
  let bit_field_to_vect_of_bits l bf =
    let v = Array.make l 0
    and nb_digit = Array.length bf in
	  match nb_digit with
    | 0 -> assert false
	  | 1 -> int_to_vect_of_bits l bf.(0)
	  | _ ->
	    for i = 0 to (nb_digit - 2) do
		    Array.blit (int_to_vect_of_bits 31 bf.(i)) 0
		      v (i * 31) 31
      done;
      let r = l mod 31 in
		  Array.blit (int_to_vect_of_bits r bf.(pred nb_digit)) 0
		    v ((pred nb_digit) * 31) r;
		  v

  (* [vect_of_bits_to_bit_field v] returns the [bit_field] encoding the
     vector of bits [v]. *)
  let vect_of_bits_to_bit_field u =
    let l = Array.length u in
    let ql = l / 31
    and rl = l mod 31 in
	  if rl = 0
	  then
	    begin
	      let v = Array.make ql 0 in
        for i=0 to (pred ql) do
		      let d = 31 * i in
		      for j=0 to 31 do
            if u.(d+j) > 0
            then v.(i) <- v.(i) + (1 lsl j)
		      done
        done;
        v
	    end
	  else
	    begin
	      let v = Array.make (succ ql) 0 in
        for i=0 to (pred ql) do
		      let d = 31 * i in
		      for j=0 to 31 do
            if (u.(d+j) > 0)
            then v.(i) <- v.(i) + (1 lsl j)
		      done
        done;
        let d = 31 * ql in
		    for j=0 to (pred rl) do
		      if (u.(d+j) > 0)
		      then v.(ql) <- v.(ql) + (1 lsl j)
		    done;
		    v
	    end

  (* [print_bit_field fmt l bf] prints the vector of [l] bits
     encoded by [bf]. *)
  let print_bit_field fmt l bf =
    let v = bit_field_to_vect_of_bits l bf in
	  fprintf fmt "[|";
	  for i=0 to (l - 2) do
	    fprintf fmt "%d ;" v.(i)
	  done;
	  fprintf fmt "%d|]" v.(pred l)
end
