(* The parser exported from thys/OCaml_Parser.thy, its tokens built from the
   lexer's: the kind, and the payload as text. *)

module P = Names.P
open Ocaml_subset

let token : Ocaml_subset.token -> (P.ocaml_tok, P.char, unit) P.token_ext =
  let k x = P.mk_token x "" and t x s = P.mk_token x (P.implode s) in
  function
  | LET -> k T_LET | REC -> k T_REC | AND -> k T_AND | IN -> k T_IN | FUN -> k T_FUN
  | FUNCTION -> k T_FUNCTION | MATCH -> k T_MATCH | WITH -> k T_WITH | TRY -> k T_TRY
  | WHEN -> k T_WHEN | AS -> k T_AS | IF -> k T_IF | THEN -> k T_THEN | ELSE -> k T_ELSE
  | BEGIN -> k T_BEGIN | END -> k T_END | TYPE -> k T_TYPE | OF -> k T_OF
  | MUTABLE -> k T_MUTABLE | OPEN -> k T_OPEN | TRUE -> k T_TRUE | FALSE -> k T_FALSE
  | LPAREN -> k T_LPAREN | RPAREN -> k T_RPAREN | LBRACKET -> k T_LBRACKET
  | RBRACKET -> k T_RBRACKET | LBRACE -> k T_LBRACE | RBRACE -> k T_RBRACE
  | SEMI -> k T_SEMI | COMMA -> k T_COMMA | BAR -> k T_BAR
  | MINUSGREATER -> k T_MINUSGREATER | EQUAL -> k T_EQUAL | MINUS -> k T_MINUS
  | STAR -> k T_STAR | COLON -> k T_COLON | COLONCOLON -> k T_COLONCOLON
  | COLONEQUAL -> k T_COLONEQUAL | DOT -> k T_DOT | LESSMINUS -> k T_LESSMINUS
  | UNDERSCORE -> k T_UNDERSCORE | QUOTE -> k T_QUOTE | AMPERAMPER -> k T_AMPERAMPER
  | BARBAR -> k T_BARBAR | BANG -> k T_BANG
  | INFIXOP0 s -> t T_INFIXOP0 s | INFIXOP1 s -> t T_INFIXOP1 s
  | INFIXOP2 s -> t T_INFIXOP2 s | INFIXOP3 s -> t T_INFIXOP3 s
  | LIDENT s -> t T_LIDENT s | UIDENT s -> t T_UIDENT s | INT s -> t T_INT s
  | FLOAT s -> t T_FLOAT s | STRING s -> t T_STRING s | CHAR s -> t T_CHAR s
  | EOF -> k T_EOF

let tokens (ts : Ocaml_subset.token array) = Array.to_list (Array.map token ts)

let parse ts =
  match P.ocaml_implementation ts with Some s -> s | None -> failwith "Isa.parse"
