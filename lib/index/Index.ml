module HMap = Type.Ident.HMap

type key = Type.Ident.t

type info = {
  ty : Type.t ;
}

type t = info HMap.t

let get = HMap.get
let add = HMap.add
let iter = HMap.iter
let make () = HMap.create 17

let make =
  Findlib.init () ;
  let stdlib_dir = Findlib.ocaml_stdlib () in
  fun ?(env = Type.Env.make ()) () ->
    let idx = make () in
    [ stdlib_dir ]
    |> LibIndex.Misc.unique_subdirs
    |> LibIndex.load
    |> LibIndex.all
    |> List.iter (fun info ->
      match info.LibIndex.kind with
      | LibIndex.Value ->
          let [@warning "-8"] Outcometree.Osig_value out_ty = Option.get info.ty in
          let out_ty = out_ty.oval_type in
          let ty = Type.of_outcometree env out_ty in
          add idx (Type.Ident.of_list @@ info.path @ [ info.name ]) { ty }
      | _ -> ()) ;
    idx

let load file_name =
  CCIO.with_in file_name Marshal.from_channel

let save self file_name =
  CCIO.with_out file_name @@ fun out -> Marshal.to_channel out self []
