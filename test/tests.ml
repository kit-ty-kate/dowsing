
let (!!) s = Imports.read (Lexing.from_string s)
let (===) s1 s2 = Typexpr.compare !!s1 !!s2 = 0

let _ =

  "'b t -> ('a -> 'd) -> 'c t" === "('a -> 'd) -> 'b t -> 'c t"
