(** Terms and Problems for AC symbols *)

type t = Pure.t array

let make p = p

type problem = {left : t ; right : t }

let make_problem left right = {left;right}

let as_tuple t : Type.t =
  match t with
  | [|x|] -> Pure.as_typexpr x
  | t ->
    Type.tuple
      (t |> Iter.of_array |> Iter.map Pure.as_typexpr |> Type.NSet.of_iter)

let pp fmt t =
  match t with
  | [|x|] -> Pure.pp fmt x
  | t ->
    Fmt.pf fmt "@[<h>(%a)@]" Fmt.(array ~sep:(unit ",@ ") Pure.pp) t

let pp_problem fmt {left ; right} =
  Fmt.pf fmt "%a = %a"
    Fmt.(array ~sep:(unit ",") Pure.pp) left
    Fmt.(array ~sep:(unit ",") Pure.pp) right
