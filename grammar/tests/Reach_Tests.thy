(* Author: Basil Fürer *)

theory Reach_Tests
  imports TIGER_Grammar.LR_Parser Parser_Check
begin

section \<open>Coverage of the error states\<close>

text \<open>Sentences of the driver against \<^file>\<open>../lr_reach.ML\<close>: every word over the
  terminals up to a length, cut at the first error, gives the same pairs of a state and
  a terminal and the same shortest lengths as the engine.\<close>

declare [[parser_errors_budget = 120]]

ML \<open>
fun coverage_of ctxt name =
  let
    val cov = the (LR_Backend.get_coverage ctxt name);
    val ((view, driver), _) = LR_Backend.evaluate_coverage ctxt (#coverage cov) [];
  in (cov, view, driver) end;

fun brute ctxt name len =
  let
    val (cov, view, driver) = coverage_of ctxt name;
    val hide = #hide cov;
    val (v, _, _) = LR_Backend.dest_view view;
    val nt = #nterms v;
    val r = LR_Reach.run {hide = hide, seconds = 30.0} v;
    fun key (s, z) = s * (nt + 1) + z;
    fun enc w = maps (fn t => [t, 0]) (rev w);
    val toks = filter (fn t => SOME t <> hide) (0 upto nt - 1);
    val seen = Unsynchronized.ref Inttab.empty;
    fun note k d = seen := Inttab.map_default (k, d) (fn e => Int.min (e, d)) (!seen);
    fun step w =
      (case driver (enc w) of
        [] => true
      | st :: tk :: _ :: idx :: _ => (note (key (st, tk)) idx; tk = nt)
      | _ => raise Fail "driver");
    fun layer n fr =
      if n > len orelse null fr then ()
      else
        let val alive = filter step fr
        in layer (n + 1) (if n = len then [] else maps (fn w => map (fn t => t :: w) toks) alive) end;
    val _ = layer 0 [[]];
    val eng = Inttab.make (map (fn {state, look, dist, ...} => (key (state, look), dist)) (#errors r));
    val seen = Inttab.dest (!seen);
    val missing = filter_out (Inttab.defined eng o fst) seen;
    val wrong = filter (fn (k, d) => Inttab.lookup eng k <> SOME d andalso Inttab.defined eng k) seen;
    val extra =
      filter (fn {state, look, dist, ...} =>
        (if look = nt then dist <= len else dist < len) andalso
        not (AList.defined (op =) seen (key (state, look)))) (#errors r);
    val _ = \<^assert> (#complete r andalso null missing andalso null wrong andalso null extra);
  in (length (#errors r), #facts r) end;
\<close>

datatype t = X | Num | Plus | Semi | LP | RP

grammar g =
  tokens \<open>t\<close>
  productions
    S :: \<open>nat\<close> = E Semi S \<Rightarrow> \<open>\<lambda>e _ s. e\<close> | E
  and
    E :: \<open>nat\<close> = E Plus T \<Rightarrow> \<open>\<lambda>a _ b. a\<close> | T
  and
    T :: \<open>nat\<close> = X \<Rightarrow> \<open>\<lambda>_. 1\<close> | Num \<Rightarrow> \<open>\<lambda>_. 2\<close> | LP E RP \<Rightarrow> \<open>\<lambda>_ e _. e\<close>

parser (diagnostics) p for g
  errors
    LP RP \<Rightarrow> \<open>m\<close>

ML \<open>\<^assert> (brute \<^context> \<^const_name>\<open>p\<close> 8 = (28, 254))\<close>

parser_error_states p
parser_error_states (token) p

text \<open>The skeleton of an \<open>errors\<close> block for the open states, one shortest sentence each.\<close>

ML \<open>
fun skeleton_of ctxt name by_token =
  let
    val (cov, view, driver) = coverage_of ctxt name;
    val hits = LR_Backend.error_hits ctxt cov (view, driver);
  in LR_Diagnostics.skeleton (#spelled cov) by_token (filter_out (LR_Diagnostics.covered (#keys cov)) hits) end;
\<close>

ML \<open>
  \<^assert> (skeleton_of \<^context> \<^const_name>\<open>p\<close> false = cat_lines
    ["errors",
     "    \"X\" \"X\" \<Rightarrow> \<open>TODO state 3\<close>",
     "  | \"Num\" \"X\" \<Rightarrow> \<open>TODO state 4\<close>",
     "  | \"LP\" \"Num\" \"RP\" \"X\" \<Rightarrow> \<open>TODO state 5\<close>",
     "  | \"LP\" \"Num\" \<Rightarrow> \<open>TODO state 6\<close>",
     "  | \"Num\" \"Semi\" \<Rightarrow> \<open>TODO state 9\<close>",
     "  | \"Num\" \"Plus\" \<Rightarrow> \<open>TODO state 11\<close>",
     "  | \"Num\" \"RP\" \<Rightarrow> \<open>TODO state 12\<close>",
     "  | \<open>[]\<close> \<Rightarrow> \<open>TODO state 13\<close>"])\<close>

datatype t2 = Ta | Tb | Tc | Td | Te | Tf | Tg

grammar g2 =
  tokens \<open>t2\<close>
  productions
    S :: \<open>nat\<close> = Ta A Tc \<Rightarrow> \<open>\<lambda>_ _ _. 0\<close> | Tb A Td \<Rightarrow> \<open>\<lambda>_ _ _. 0\<close> | L Te \<Rightarrow> \<open>\<lambda>_ _. 0\<close>
  and
    A :: \<open>nat\<close> = Tg \<Rightarrow> \<open>\<lambda>_. 0\<close>
  and
    L :: \<open>nat\<close> = \<Rightarrow> \<open>0\<close> | L I \<Rightarrow> \<open>\<lambda>_ _. 0\<close>
  and
    I :: \<open>nat\<close> = Tf O Ta \<Rightarrow> \<open>\<lambda>_ _ _. 0\<close>
  and
    O :: \<open>nat\<close> = \<Rightarrow> \<open>0\<close> | Tb \<Rightarrow> \<open>\<lambda>_. 0\<close>

parser (diagnostics) p2 for g2

ML \<open>\<^assert> (brute \<^context> \<^const_name>\<open>p2\<close> 9 = (66, 47))\<close>

text \<open>The error token: states only it reaches are no error states.\<close>

datatype t3 = X3 | Plus3 | Semi3 | Err3

grammar g3 =
  tokens \<open>t3\<close>
  productions
    S :: \<open>nat\<close> = E Semi3 S \<Rightarrow> \<open>\<lambda>e _ s. e\<close> | E | Err3 Semi3 S \<Rightarrow> \<open>\<lambda>_ _ s. s\<close>
  and
    E :: \<open>nat\<close> = E Plus3 X3 \<Rightarrow> \<open>\<lambda>a _ _. a\<close> | X3 \<Rightarrow> \<open>\<lambda>_. 1\<close>

parser (diagnostics) p3 for g3 recover Err3

ML \<open>\<^assert> (brute \<^context> \<^const_name>\<open>p3\<close> 9 = (11, 53))\<close>

parser_error_states p3

text \<open>The skeleton of \<open>p\<close> pasted: every error state has a message now.\<close>

parser (diagnostics) p_full for g
  errors
    LP RP \<Rightarrow> \<open>m\<close>
  | "X" "X" \<Rightarrow> \<open>an operand is followed by another operand\<close>
  | "Num" "X" \<Rightarrow> \<open>a number is followed by an operand\<close>
  | "LP" "Num" "RP" "X" \<Rightarrow> \<open>a parenthesis is followed by an operand\<close>
  | "LP" "Num" \<Rightarrow> \<open>a parenthesis is not closed\<close>
  | "Num" "Semi" \<Rightarrow> \<open>a statement is missing after ';'\<close>
  | "Num" "Plus" \<Rightarrow> \<open>an operand is missing after '+'\<close>
  | "Num" "RP" \<Rightarrow> \<open>a ')' without '('\<close>
  | \<open>[]\<close> \<Rightarrow> \<open>the input is empty\<close>

ML \<open>\<^assert> (length (#keys (the (LR_Backend.get_coverage \<^context> \<^const_name>\<open>p_full\<close>))) = 9)\<close>

text \<open>The same with a key for each pair, and a key that does not count.\<close>

parser (diagnostics) p_key for g
  errors
    LP RP (token) \<Rightarrow> \<open>m\<close>
  | LP RP (shift) \<Rightarrow> \<open>n\<close>

ML \<open>
  let val c = the (LR_Backend.get_coverage \<^context> \<^const_name>\<open>p_key\<close>)
  in \<^assert> (length (#keys c) = 1 andalso #shifts c = 1) end\<close>

section \<open>A grammar with columns\<close>

datatype tok = While | Colon | Id

grammar py =
  tokens \<open>tok\<close>
  terminals "while" = \<open>While\<close> and ":" = \<open>Colon\<close>
  productions
      Prog :: \<open>nat\<close> = Block
    and
      Block :: \<open>nat\<close>
        = Stmt\<^sup>=
        | Block\<^sup>= Stmt\<^sup>=  \<Rightarrow> \<open>(+)\<close>
    and
      Stmt :: \<open>nat\<close>
        = Id\<^sup>=                      \<Rightarrow> \<open>\<lambda>_. 1\<close>
        | "while"\<^sup>= Id\<^sup>> ":"\<^sup>> Block\<^sup>>  \<Rightarrow> \<open>\<lambda>_ n. n + 1\<close>

parser (diagnostics) py_p for py
  errors
    "while"@1 Id@7 ":"@8 Id@3 Id@4 \<Rightarrow> \<open>Statements of a suite line up.\<close>

parser_error_states py_p

text \<open>The driver on every word up to a length in every order of its columns meets
  no error outside the list.\<close>

ML \<open>
fun brute_columns ctxt name len =
  let
    val (cov, view, driver) = coverage_of ctxt name;
    val hits = LR_Backend.error_hits ctxt cov (view, driver);
    val listed = map (fn {state, look, ...} => (state, look)) hits;
    val nt = length (#spelled cov);
    val seen = Unsynchronized.ref [];
    fun choices [] = [0, 8]
      | choices cs =
          let
            val s = sort_distinct int_ord cs;
            fun mids (a :: (r as b :: _)) = (a + b) div 2 :: mids r
              | mids _ = [];
          in s @ mids s @ [List.last s + 64] @ (if hd s > 1 then [hd s div 2] else []) end;
    fun go w =
      List.app (fn t => List.app (fn c =>
        let val w' = w @ [(t, c)]
        in
          (case driver (maps (fn (a, b) => [a, b]) w') of
            [] => if length w' < len then go w' else ()
          | st :: tk :: _ =>
              (seen := insert (op =) (st, tk) (!seen);
               if tk = nt andalso length w' < len then go w' else ())
          | _ => raise Fail "driver")
        end) (choices (map snd w))) (0 upto nt - 1);
    val _ = go [];
  in (length listed, length (!seen), subtract (op =) listed (!seen)) end;
\<close>

ML \<open>\<^assert> (#3 (brute_columns \<^context> \<^const_name>\<open>py_p\<close> 6) = [])\<close>

section \<open>\<open>on_error_reduce\<close>\<close>

text \<open>The error after a statement of a suite: without the option in the state of the
  token, with it in the state after the reductions.\<close>

definition col :: \<open>nat \<Rightarrow> 't \<Rightarrow> ('t, unit) token\<close> where
  \<open>col c t = \<lparr>tok = t, span = span.make 0 c c 1 []\<rparr>\<close>

parser (diagnostics) py_o for py
  on_error_reduce Stmt Block
  errors
    "while"@1 Id@7 ":"@8 Id@3 ":"@9 \<Rightarrow> \<open>after a suite\<close>

ML \<open>val _ = @{thms py_o_diag.Inr_iff}\<close>

definition py_w where \<open>py_w = [col 1 While, col 7 Id, col 8 Colon, col 3 Id, col 9 Colon]\<close>

parser_check \<open>(case (py_o_diag_base py_w, py_o_diag py_w) of
    (Inl a, Inl b) \<Rightarrow> pe_state a \<noteq> pe_state b \<and> pe_index a = pe_index b
  | _ \<Rightarrow> False)\<close>

parser_check \<open>py_o [col 1 While, col 7 Id, col 8 Colon, col 3 Id] = py_p [col 1 While, col 7 Id, col 8 Colon, col 3 Id]\<close>

text \<open>With recovery the report is the one of \<open>p_diag\<close>, the repair the plain one.\<close>

datatype tr = RId | RColon | RErr

grammar pr =
  tokens \<open>tr\<close>
  productions
      Block :: \<open>nat\<close>
        = Stmt\<^sup>=
        | Block\<^sup>= Stmt\<^sup>=  \<Rightarrow> \<open>(+)\<close>
    and
      Stmt :: \<open>nat\<close>
        = RId\<^sup>= \<Rightarrow> \<open>\<lambda>_. 1\<close>
        | RId\<^sup>= RColon\<^sup>> Block\<^sup>> \<Rightarrow> \<open>\<lambda>_ _ n. n\<close>
        | RErr\<^sup>= \<Rightarrow> \<open>\<lambda>_. 0\<close>

parser (diagnostics) pr_o for pr recover RErr on_error_reduce Stmt

definition pr_w where \<open>pr_w = [col 0 RId, col 2 RColon, col 4 RId, col 6 RColon, col 8 RColon]\<close>

parser_check \<open>(case (fst (pr_o_repair pr_w), pr_o_diag pr_w) of
    (a # _, Inl b) \<Rightarrow> pe_state a = pe_state b | _ \<Rightarrow> False)\<close>

text \<open>The sparse and the dense drivers.\<close>

datatype cf_tok = CA | CB | CErr

grammar cf =
  tokens \<open>cf_tok\<close>
  productions S :: \<open>nat\<close> = X CB \<Rightarrow> \<open>\<lambda>x _. x\<close> | Y CB \<Rightarrow> \<open>\<lambda>y _. y\<close>
    and X :: \<open>nat\<close> = CA \<Rightarrow> \<open>\<lambda>_. 0\<close> | CErr \<Rightarrow> \<open>\<lambda>_. 1\<close>
    and Y :: \<open>nat\<close> = CErr \<Rightarrow> \<open>\<lambda>_. 2\<close>

parser (diagnostics) cf_p for cf recover CErr
  errors CB \<Rightarrow> \<open>m\<close>

parser_error_states cf_p

datatype dc_tok = DA | DB | DC

grammar dc =
  tokens \<open>dc_tok\<close>
  productions S :: \<open>nat\<close> = X DB \<Rightarrow> \<open>\<lambda>x _. x\<close> | DC D \<Rightarrow> \<open>\<lambda>_ d. d\<close>
    and X :: \<open>nat\<close> = DA \<Rightarrow> \<open>\<lambda>_. 0\<close>
    and D :: \<open>nat\<close> = D \<Rightarrow> \<open>\<lambda>d. d\<close> | DB \<Rightarrow> \<open>\<lambda>_. 2\<close>

parser (diagnostics) dc_o for dc on_error_reduce X
  errors DA DA \<Rightarrow> \<open>m\<close>

parser_check \<open>(case dc_o_diag [col 0 DA, col 2 DA] of Inl e \<Rightarrow> pe_index e = 1 | _ \<Rightarrow> False)\<close>

text \<open>The simple driver ignores it, with a warning.\<close>

parser (diagnostics) p_o for g on_error_reduce T
  errors LP RP \<Rightarrow> \<open>m\<close>

section \<open>Tokens with further fields\<close>

record tt = \<open>(t, unit) token\<close> +
  mark :: nat

grammar gt =
  tokens \<open>tt\<close>
  productions
    S :: \<open>nat\<close> = X Plus X \<Rightarrow> \<open>\<lambda>a _ b. mark a\<close>

parser (diagnostics) p_t for gt
  token_info \<open>\<lambda>_. tt.fields 7\<close>
  errors X X \<Rightarrow> \<open>m\<close>

parser_error_states p_t

text \<open>Without it the sentences are not run, and the pairs are still listed.\<close>

parser (diagnostics) p_u for gt
  errors \<open>[\<lparr>tok = X, span = span.make 0 0 0 1 [], mark = 0\<rparr>, \<lparr>tok = X, span = span.make 0 2 2 1 [], mark = 0\<rparr>]\<close> \<Rightarrow> \<open>m\<close>

end
