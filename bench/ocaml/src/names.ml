module P = Ocaml_parser.OCaml_Parser

let binop = P.binop
let mk_fun = P.mk_fun
let cons_exp = P.cons_exp
let list_exp = P.list_exp
let cons_pat = P.cons_pat
let list_pat = P.list_pat

let eq = P.explode "="
let minus = P.explode "-"
let star = P.explode "*"
let neg = P.explode "~-"
let bang = P.explode "!"
let colonequal = P.explode ":="
let barbar = P.explode "||"
let amperamper = P.explode "&&"
let true_ = P.explode "true"
let false_ = P.explode "false"
let unit = P.explode "()"
let nil = P.explode "[]"
