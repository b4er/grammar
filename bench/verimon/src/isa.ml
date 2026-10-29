(* The parser exported from thys/VeriMon_Parser.thy: its tokens built from the
   lexer's, its formulas converted to MonPoly's MFOTL.formula.  The conversion
   does what the original's actions do with numbers and string constants,
   assertions included. *)

module P = Verimon_parser.VeriMon_Parser
open Predicate
open MFOTL

let kind : Formula_parser.token -> P.mtok = function
  | FALSE -> T_FALSE | TRUE -> T_TRUE | LPA -> T_LPA | RPA -> T_RPA | LSB -> T_LSB
  | RSB -> T_RSB | COM -> T_COM | SC -> T_SC | DOT -> T_DOT | QM -> T_QM | LD -> T_LD
  | LESSEQ -> T_LESSEQ | EQ -> T_EQ | LESS -> T_LESS | GTR -> T_GTR | GTREQ -> T_GTREQ
  | STAR -> T_STAR | LARROW -> T_LARROW | PLUS -> T_PLUS | MINUS -> T_MINUS
  | SLASH -> T_SLASH | MOD -> T_MOD | F2I -> T_F2I | I2F -> T_I2F
  | STR _ -> T_STR | STR_CST _ -> T_STR_CST | INT _ -> T_INT | RAT _ -> T_RAT | TU _ -> T_TU
  | LET -> T_LET | IN -> T_IN | NOT -> T_NOT | AND -> T_AND | OR -> T_OR | IMPL -> T_IMPL
  | EQUIV -> T_EQUIV | EX -> T_EX | FA -> T_FA | PREV -> T_PREV | NEXT -> T_NEXT
  | EVENTUALLY -> T_EVENTUALLY | ONCE -> T_ONCE | ALWAYS -> T_ALWAYS
  | PAST_ALWAYS -> T_PAST_ALWAYS | SINCE -> T_SINCE | UNTIL -> T_UNTIL | BAR -> T_BAR
  | FREX -> T_FREX | PREX -> T_PREX | CNT -> T_CNT | MIN -> T_MIN | MAX -> T_MAX
  | SUM -> T_SUM | AVG -> T_AVG | MED -> T_MED | END -> T_END
  | EOF -> invalid_arg "Isa.kind: EOF"

(* the payload: numbers exactly (%h), `_` numbered by its position, as the
   original's counter numbers them in order *)
let text i : Formula_parser.token -> string = function
  | STR s | STR_CST s -> s
  | INT x | RAT x -> Printf.sprintf "%h" x
  | TU (n, c) -> Printf.sprintf "%d%c" n c
  | LD -> "_" ^ string_of_int (i + 1)
  | _ -> ""

let tokens (ts : Formula_parser.token array) =
  Array.to_list (Array.mapi (fun i t -> P.mk_token (kind t) (text i t)) ts)

let str = P.implode

(* the original's actions on numbers and string constants *)
let cst : P.mcst -> cst = function
  | CInt s ->
      let x = float_of_string (str s) in
      assert (x < float_of_int max_int);
      assert (x > float_of_int min_int);
      Int (int_of_float x)
  | CRat s -> Float (float_of_string (str s))
  | CStr s ->
      let s = str s in
      let len = String.length s in
      assert (s.[0] = '\"' && s.[len - 1] = '\"');
      Str (String.sub s 1 (len - 2))

let rec term : P.mterm -> Predicate.term = function
  | TVar v -> Var (str v)
  | TCst c -> Cst (cst c)
  | TF2i t -> F2i (term t)
  | TI2f t -> I2f (term t)
  | TPlus (a, b) -> Plus (term a, term b)
  | TMinus (a, b) -> Minus (term a, term b)
  | TUMinus t -> UMinus (term t)
  | TMult (a, b) -> Mult (term a, term b)
  | TDiv (a, b) -> Div (term a, term b)
  | TMod (a, b) -> Mod (term a, term b)

let units : P.munits -> float = function
  | UNum s -> float_of_string (str s)
  | UTime s ->
      let n, c = Scanf.sscanf (str s) "%d%c" (fun n c -> (n, c)) in
      let d = match c with
        | 'd' -> 24 * 60 * 60 | 'h' -> 60 * 60 | 'm' -> 60 | 's' -> 1
        | _ -> failwith "unrecognized time unit" in
      float_of_int (d * n)

let bound : P.mbound -> bound = function
  | OBnd u -> OBnd (units u)
  | CBnd u -> CBnd (units u)
  | BInf -> Inf

let intv (a, b) = (bound a, bound b)

let agg : P.magg -> agg_op = function
  | ACnt -> Cnt | AMin -> Min | AMax -> Max | ASum -> Sum | AAvg -> Avg | AMed -> Med

let pred n ts = let ts = List.map term ts in (str n, List.length ts, ts)
let vars = List.map str

let rec formula : P.mformula -> MFOTL.formula = function
  | FEqual (a, b) -> Equal (term a, term b)
  | FLess (a, b) -> Less (term a, term b)
  | FLessEq (a, b) -> LessEq (term a, term b)
  | FPred (n, ts) -> Pred (pred n ts)
  | FLet (n, ts, a, b) -> Let (pred n ts, formula a, formula b)
  | FNeg f -> Neg (formula f)
  | FAnd (a, b) -> And (formula a, formula b)
  | FOr (a, b) -> Or (formula a, formula b)
  | FImplies (a, b) -> Implies (formula a, formula b)
  | FEquiv (a, b) -> Equiv (formula a, formula b)
  | FExists (vs, f) -> Exists (vars vs, formula f)
  | FForAll (vs, f) -> ForAll (vars vs, formula f)
  | FAggreg (y, op, x, g, f) ->
      Aggreg (TSymb (TAny, 0), str y, agg op, str x, vars g, formula f)
  | FPrev (i, f) -> Prev (intv i, formula f)
  | FNext (i, f) -> Next (intv i, formula f)
  | FEventually (i, f) -> Eventually (intv i, formula f)
  | FOnce (i, f) -> Once (intv i, formula f)
  | FAlways (i, f) -> Always (intv i, formula f)
  | FPastAlways (i, f) -> PastAlways (intv i, formula f)
  | FSince (i, a, b) -> Since (intv i, formula a, formula b)
  | FUntil (i, a, b) -> Until (intv i, formula a, formula b)

(* no parse, or an action that rejects: Failure *)
let parse ts =
  match P.verimon_parse ts with
  | Some (Some f) -> formula f
  | _ -> failwith "Isa.parse"
