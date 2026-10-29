(*
  Driver for the exported Isabelle parser (pure_bench.ML, module Pure_Bench).
  Reads a token dump of `purebench tokens FILE` (class, row, column, payload
  with qstr escapes \" \\ \NNN;) and mirrors purebench's modes:

    isabelle ast TOKFILE          prints the AST as purebench ast does
    isabelle parse TOKFILE REPS   parses REPS times, prints the sum of
                                       bench_ok (0 no parse, 1 no AST, 2 ok)
*)

fun unquote s =
  let
    val cs = String.explode s
    fun digits acc (#";" :: r) = (acc, r)
      | digits acc (c :: r) = digits (acc * 10 + (Char.ord c - 48)) r
      | digits _ [] = raise Fail "bad escape"
    fun go (#"\\" :: #"\"" :: r) acc = go r (#"\"" :: acc)
      | go (#"\\" :: #"\\" :: r) acc = go r (#"\\" :: acc)
      | go (#"\\" :: r) acc =
          let val (n, r') = digits 0 r in go r' (Char.chr n :: acc) end
      | go [#"\""] acc = String.implode (rev acc)
      | go (c :: r) acc = go r (c :: acc)
      | go [] _ = raise Fail "unterminated string"
  in
    case cs of #"\"" :: r => go r [] | _ => raise Fail ("bad payload " ^ s)
  end

fun read_token line =
  let
    val line = if String.isSuffix "\n" line
               then String.substring (line, 0, size line - 1) else line
    fun field s =
      let val (a, b) = Substring.splitl (fn c => c <> #" ") s
      in (Substring.string a, Substring.triml 1 b) end
    val (cls, r1) = field (Substring.full line)
    val (row, r2) = field r1
    val (col, r3) = field r2
    fun int s = valOf (IntInf.fromString s)
  in
    Pure_Bench.mk_tok cls (int row) (int col) (unquote (Substring.string r3))
  end

fun read_tokens file =
  let
    val ins = TextIO.openIn file
    fun loop acc =
      case TextIO.inputLine ins of
        NONE => (TextIO.closeIn ins; rev acc)
      | SOME l => loop (read_token l :: acc)
  in loop [] end

fun parse_loop n toks acc =
  if n <= 0 then acc
  else parse_loop (n - 1) toks (acc + Pure_Bench.bench_ok toks)

fun main () =
  case CommandLine.arguments () of
    ["ast", f] => TextIO.print (Pure_Bench.bench_ast (read_tokens f))
  | ["parse", f, reps] =>
      TextIO.print (IntInf.toString
        (parse_loop (valOf (Int.fromString reps)) (read_tokens f) 0) ^ "\n")
  | _ => (TextIO.output (TextIO.stdErr,
            "usage: isabelle ast TOKFILE | parse TOKFILE REPS\n");
          OS.Process.exit OS.Process.failure)
