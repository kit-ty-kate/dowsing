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
   Boolean operations are provided : interface.

   $Id: bit_field.mli 4 2004-10-19 14:04:20Z contejea $

 ***************************************************************************)

open Format

module type S =
sig
  type t

    (*

      [all_zero n] returns a bit filed of size n filled with 0.
      [all_one n] returns a bit filed of size n filled with 1.

    *)

  val all_zero : int ->  t
  val all_one  : int ->  t

      (*

size of a bit field

      *)

  val bit_length : t -> int

      (*

boolean operations. bit fields have to be the same length.

      *)

  val bit_and : t -> t -> t
  val bit_or : t -> t -> t
  val bit_not : t -> t

      (*
[bit_nth n l] returns a [bit_field] encoding a vector of bits of
length 31*l where all the bits are equal to 0, except at position
[n] which is a 1.
\begin{verbatim}
                     (0,...,0,1,0,...,0)
                      ^       ^       ^
                      |       |       |
                      0       n    (31*l) -1
	   \end{verbatim}
	   [bit_nth_first n l] returs a [bit_field] encoding a vector of bits of
	   length 31*l where the first nth bits are equal to 1, the others
	   being equal to 0.
	   \begin{verbatim}
                     (1,...,1,1,0,...,0)
                      ^       ^       ^
                      |       |       |
                      0       n    (31*l) -1
	   \end{verbatim}
   *)

  val bit_nth : int -> int -> t
  val bit_nth_first : int -> int -> t

      (*

[is_zero b] returns [true] if the bit field [b] encodes the integer
0 in base 2.

[atmost_one_one b] returns [true] if the bit field [b] encodes a
power of 2 in base 2.

      *)

  val is_zero : t -> bool;;
  val atmost_one_one : t -> bool;;

  (*

    [bit_field_to_vect_of_bits l bf] returns the vector of bits of length l
    encoded by the [bit_field] [bf].

    [vect_of_bits_to_bit_field v] returns the [bit_field] encoding the
    vector of bits [v].

  *)

  val bit_field_to_vect_of_bits : int -> t -> int array
  val vect_of_bits_to_bit_field : int array -> t

      (*

pretty-prints a bit field in the current formating box

      *)

  val print_bit_field : formatter -> int -> t -> unit

end

module Small : S with type t = int

module Large : S with type t = int array
