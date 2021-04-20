type t = {
  args: ACTerm.t;
  ret: Type.t;
}

type problem = {
  left: t;
  right: t;
}

let make args ret : t = {args; ret}
let make_problem left right = {left; right}

let pp_problem namefmt fmt self =
  Fmt.pf fmt "%a -> %a = %a -> %a"
    Fmt.(array ~sep:(unit " * ") @@ Pure.pp namefmt) self.left.args
    (Type.pp namefmt) self.left.ret
    Fmt.(array ~sep:(unit " * ") @@ Pure.pp namefmt) self.right.args
    (Type.pp namefmt) self.right.ret
