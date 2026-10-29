(* A lexer for the subset, after OCaml's parsing/lexer.mll, producing the
   Menhir parser's tokens.  It differs from OCaml's where the subset has
   fewer token kinds: "<" and ">" are INFIXOP0, "+", "-." and "+." are
   INFIXOP2, and keywords and operators outside the subset are errors, so
   that every input it accepts is one OCaml reads the same way.  A string's
   or a character's payload is its value, escapes decoded as OCaml does. *)
{
open Ocaml_subset

exception Error of string

let x = Names.P.explode

let keyword = function
  | "let" -> Some LET | "rec" -> Some REC | "and" -> Some AND | "in" -> Some IN
  | "fun" -> Some FUN | "function" -> Some FUNCTION | "match" -> Some MATCH
  | "with" -> Some WITH | "try" -> Some TRY | "when" -> Some WHEN | "as" -> Some AS
  | "if" -> Some IF | "then" -> Some THEN | "else" -> Some ELSE
  | "begin" -> Some BEGIN | "end" -> Some END | "type" -> Some TYPE | "of" -> Some OF
  | "mutable" -> Some MUTABLE | "open" -> Some OPEN
  | "true" -> Some TRUE | "false" -> Some FALSE
  | "mod" | "land" | "lor" | "lxor" as s -> Some (INFIXOP3 (x s))
  | "asr" | "lsl" | "lsr" | "or" | "assert" | "class" | "constraint" | "do" | "done"
  | "downto" | "effect" | "exception" | "external" | "for" | "functor" | "include"
  | "inherit" | "initializer" | "lazy" | "method" | "module" | "new" | "nonrec"
  | "object" | "private" | "sig" | "struct" | "to" | "val" | "virtual" | "while" as s ->
      raise (Error ("keyword outside the subset: " ^ s))
  | _ -> None

let error lexbuf what =
  raise (Error (Printf.sprintf "%s at offset %d" what (Lexing.lexeme_start lexbuf)))

let escape = function 'n' -> '\n' | 't' -> '\t' | 'b' -> '\b' | 'r' -> '\r' | c -> c

let char_of_code lexbuf n =
  if n > 255 then error lexbuf "illegal escape" else Char.chr n
}

let blank = [' ' '\t' '\r' '\n']
let lower = ['a'-'z' '_']
let upper = ['A'-'Z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']
let symbolchar = ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~']
let decimal = ['0'-'9'] ['0'-'9' '_']*
let int = decimal
  | '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f'] ['0'-'9' 'A'-'F' 'a'-'f' '_']*
  | '0' ['o' 'O'] ['0'-'7'] ['0'-'7' '_']*
  | '0' ['b' 'B'] ['0'-'1'] ['0'-'1' '_']*
let float = decimal ('.' ['0'-'9' '_']*)? (['e' 'E'] ['+' '-']? decimal)?

rule token = parse
  | blank+ { token lexbuf }
  | "(*" { comment 0 lexbuf; token lexbuf }
  | "_" { UNDERSCORE }
  | lower identchar* as s { match keyword s with Some k -> k | None -> LIDENT (x s) }
  | upper identchar* as s { UIDENT (x s) }
  | int as s { INT (x s) }
  | float as s { FLOAT (x s) }
  | '"' { let b = Buffer.create 16 in string b lexbuf; STRING (x (Buffer.contents b)) }
  | "'" ([^ '\\' '\'' '\010' '\013'] as c) "'" { CHAR (x (String.make 1 c)) }
  | "'\\" (['\\' '\'' '"' 'n' 't' 'b' 'r' ' '] as c) "'" { CHAR (x (String.make 1 (escape c))) }
  | "'\\" (['0'-'9'] ['0'-'9'] ['0'-'9'] as d) "'"
      { CHAR (x (String.make 1 (char_of_code lexbuf (int_of_string d)))) }
  | "'\\x" (['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F'] as h) "'"
      { CHAR (x (String.make 1 (Char.chr (int_of_string ("0x" ^ h))))) }
  | "'" { QUOTE }
  | "(" { LPAREN } | ")" { RPAREN } | "[" { LBRACKET } | "]" { RBRACKET }
  | "{" { LBRACE } | "}" { RBRACE } | ";" { SEMI } | "," { COMMA } | "|" { BAR }
  | "->" { MINUSGREATER } | "=" { EQUAL } | "-" { MINUS } | "*" { STAR }
  | ":" { COLON } | "::" { COLONCOLON } | ":=" { COLONEQUAL } | "." { DOT }
  | "<-" { LESSMINUS } | "&&" { AMPERAMPER } | "||" { BARBAR } | "!" { BANG }
  | "!=" { INFIXOP0 (x "!=") }
  (* OCaml's own tokens that are not operators of these classes *)
  | ";;" | "[|" | "|]" | "[<" | "[>" | "{<" | ">}" | ">]" | "&" | "#" | "~" | "?"
  | ".." | ":>" | "**" symbolchar* | "!" symbolchar+ | ['~' '?'] symbolchar+
      { error lexbuf ("token outside the subset: " ^ Lexing.lexeme lexbuf) }
  | ['=' '<' '>' '|' '&' '$'] symbolchar* as s { INFIXOP0 (x s) }
  | ['@' '^'] symbolchar* as s { INFIXOP1 (x s) }
  | ['+' '-'] symbolchar* as s { INFIXOP2 (x s) }
  | ['*' '/' '%'] symbolchar* as s { INFIXOP3 (x s) }
  | eof { EOF }
  | _ { error lexbuf ("unexpected " ^ Lexing.lexeme lexbuf) }

and comment depth = parse
  | "(*" { comment (depth + 1) lexbuf }
  | "*)" { if depth > 0 then comment (depth - 1) lexbuf }
  | '"' { string (Buffer.create 16) lexbuf; comment depth lexbuf }
  | eof { error lexbuf "unterminated comment" }
  | _ { comment depth lexbuf }

and string b = parse
  | '"' { () }
  | "\\" '\n' [' ' '\t']* { string b lexbuf }
  | "\\" (['\\' '\'' '"' 'n' 't' 'b' 'r' ' '] as c) { Buffer.add_char b (escape c); string b lexbuf }
  | "\\" (['0'-'9'] ['0'-'9'] ['0'-'9'] as d)
      { Buffer.add_char b (char_of_code lexbuf (int_of_string d)); string b lexbuf }
  | "\\x" (['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F'] as h)
      { Buffer.add_char b (Char.chr (int_of_string ("0x" ^ h))); string b lexbuf }
  | "\\" { error lexbuf "illegal escape" }
  | eof { error lexbuf "unterminated string" }
  | _ as c { Buffer.add_char b c; string b lexbuf }
