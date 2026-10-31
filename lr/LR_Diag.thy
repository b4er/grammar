theory LR_Diag
  imports LR_Plain LR_Sparse LR_Vec
begin

section \<open>Diagnosing a rejected word\<close>

text \<open>When the parser rejects a word, the diagnostics rerun its steps and stop
  where the run fails. Nothing here is proved about errors: the parser's
  result decides acceptance, and the diagnostics only describe a rejection.\<close>

subsection \<open>The error\<close>

text \<open>A set of columns as a list of intervals, ascending: \<open>(a, Some b)\<close> is
  \<open>{a..b}\<close>, \<open>(a, None)\<close> is \<open>{a..}\<close>.\<close>

type_synonym colset = \<open>(nat \<times> nat option) list\<close>

text \<open>The kind of a failure: the step function has no action
  (\<open>NoAction\<close>), or the loop check finds a configuration that repeats between
  two shifts (\<open>ReduceCycle\<close>). On a layout grammar the offending token may be
  accepted at another column: \<open>Offside\<close> when the accepted column nearest to
  it lies in an interval unbounded to the right (it must be indented further, a
  \<open>>\<close> or \<open>\<ge>\<close> relation), \<open>Misaligned\<close> when that interval is bounded (it
  must be aligned, a \<open>=\<close> relation); each carries all accepted columns.\<close>

datatype perr_kind = NoAction | ReduceCycle | Offside colset | Misaligned colset

text \<open>The error, over the token type of the parser's input, so that a token
  record extended by the user (\<open>'m\<close>) keeps its fields: the index of the
  offending token in the input, the token (\<open>None\<close> at the end of the input),
  the state on top of the stack where the error is detected (after the
  reductions the offending token triggered: the state that hand-written messages
  are keyed on, Pottier 2016), the kind, the terminals that would have been
  accepted in place of the offending token, and whether the end of the input
  would have been. On a layout grammar also each expected terminal with the
  columns at which it would have been accepted, and for \<^const>\<open>Offside\<close> or
  \<^const>\<open>Misaligned\<close> the token the offending one must be indented from or
  aligned with; both are empty for a grammar without layout. Last, for the
  messages: the state after the last shift, before those reductions (the state
  whose kernel says what was being parsed), and the stack where the error is
  detected, top first, each entry as its symbol and the spans of its tokens
  (Pottier's \<open>$0, $1, \<dots>\<close>: what was recognised up to here).\<close>

record ('n, 't, 'ch, 'm) perr =
  pe_index :: nat
  pe_tok :: \<open>('t, 'ch, 'm) token_scheme option\<close>
  pe_state :: nat
  pe_kind :: perr_kind
  pe_expected :: \<open>'t list\<close>
  pe_expect_end :: bool
  pe_columns :: \<open>('t \<times> colset) list\<close>
  pe_anchor :: \<open>('t, 'ch, 'm) token_scheme option\<close>
  pe_shift_state :: nat
  pe_stack :: \<open>(('n, 't) sym \<times> 'ch span list) list\<close>

subsection \<open>The engine\<close>

text \<open>The engine works on any configuration type \<open>'c\<close>, given the step
  \<open>ctl\<close>, the final test \<open>fin\<close>, the key of a configuration for the loop check
  (between shifts the input does not change, so the stack suffices), the
  remaining input and the token of an input element. It carries the AST stack
  as \<^const>\<open>brun\<close> does, and the configuration right after the last shift. The
  loop check is \<^const>\<open>brun\<close>'s (Brent's method, \<^const>\<open>bupd\<close>). Termination is
  not proved, as for \<^const>\<open>brun\<close>.\<close>

datatype ('c, 'a) dstop =
    DDone \<open>'c \<times> 'a list\<close>
  | DStuck perr_kind \<open>'c \<times> 'a list\<close> \<open>'c \<times> 'a list\<close>

partial_function (option) drun_diag ::
  \<open>('c \<Rightarrow> (('n, 't) dact \<times> 'c) option) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'k list) \<Rightarrow>
    ('c \<Rightarrow> 'w list) \<Rightarrow> ('w \<Rightarrow> ('t, 'ch, 'm) token_scheme) \<Rightarrow> 'k list option \<times> nat \<times> nat \<Rightarrow>
    'c \<times> ('m, 'ch, 'n, 't) ast list \<Rightarrow> 'c \<times> ('m, 'ch, 'n, 't) ast list \<Rightarrow>
    ('c, ('m, 'ch, 'n, 't) ast) dstop option\<close>
  where
  \<open>drun_diag ctl fin key inp dec d sh st = (case st of (c, tstk) \<Rightarrow>
     if fin c then Some (DDone st)
     else if fst d = Some (key c) then Some (DStuck ReduceCycle st sh)
     else (case ctl c of
       None \<Rightarrow> Some (DStuck NoAction st sh)
     | Some (act, c') \<Rightarrow>
         let st' = (c', xtree dec act (inp c) tstk)
         in if act = DShift then drun_diag ctl fin key inp dec (None, 1, 1) st' st'
            else drun_diag ctl fin key inp dec (bupd d (key c)) sh st'))\<close>

lemmas drun_diag_simps [code] = drun_diag.simps

subsection \<open>The expected terminals\<close>

text \<open>What would have been accepted at the error is computed on the actual
  stack, not read off a state: a trial starts from the configuration right
  after the last shift, before any reduction the offending token triggered, with
  a candidate as the lookahead, and runs the step until it shifts the candidate
  (expected), fails or repeats a configuration (not expected). For the end of
  the input the trial runs until the final test holds instead. Only reductions
  come before that shift, so a trial is short; its loop check starts afresh.
  This avoids both errors of a static reading (Pottier 2016, Sect. 4): an
  LALR state merges lookaheads that are not valid on this stack, and the
  reductions on the offending token commit to one reading and lose
  futures that were valid before them.

  The set is what \<^emph>\<open>this\<close> parser accepts: where the tables keep a conflict,
  the step takes the first licensed candidate, and so does the trial.\<close>

partial_function (option) dtrial ::
  \<open>('c \<Rightarrow> (('n, 't) dact \<times> 'c) option) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'k list) \<Rightarrow>
    'k list option \<times> nat \<times> nat \<Rightarrow> 'c \<Rightarrow> bool option\<close>
  where
  \<open>dtrial ctl fin key d c =
     (if fin c then Some True
      else if fst d = Some (key c) then Some False
      else (case ctl c of
        None \<Rightarrow> Some False
      | Some (act, c') \<Rightarrow>
          if act = DShift then Some True else dtrial ctl fin key (bupd d (key c)) c'))\<close>

lemmas dtrial_simps [code] = dtrial.simps

text \<open>The candidates that pass their trial, and whether the end of the input
  does; \<open>la\<close> sets the lookahead of the saved configuration to a candidate
  (\<open>Some\<close>) or to the end of the input (\<open>None\<close>).\<close>

definition dexpect :: \<open>('c \<Rightarrow> (('n, 't) dact \<times> 'c) option) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'k list) \<Rightarrow>
    ('x option \<Rightarrow> 'c) \<Rightarrow> 'x list \<Rightarrow> 'x list \<times> bool\<close> where
  \<open>dexpect ctl fin key la xs =
     (filter (\<lambda>x. dtrial ctl fin key (None, 1, 1) (la (Some x)) = Some True) xs,
      dtrial ctl fin key (None, 1, 1) (la None) = Some True)\<close>

text \<open>The stack of an error: each tree as its root symbol and the spans of its
  tokens, in input order.\<close>

fun aspans :: \<open>('m, 'ch, 'n, 't) ast \<Rightarrow> 'ch span list \<Rightarrow> 'ch span list\<close>
  and aspanss :: \<open>('m, 'ch, 'n, 't) ast list \<Rightarrow> 'ch span list \<Rightarrow> 'ch span list\<close> where
  \<open>aspans (Leaf x) acc = span x # acc\<close>
| \<open>aspans (Node n ts) acc = aspanss ts acc\<close>
| \<open>aspanss [] acc = acc\<close>
| \<open>aspanss (t # ts) acc = aspans t (aspanss ts acc)\<close>

fun aroot :: \<open>('m, 'ch, 'n, 't) ast \<Rightarrow> ('n, 't) sym\<close> where
  \<open>aroot (Leaf x) = Tm (tok x)\<close>
| \<open>aroot (Node n ts) = Nt n\<close>

definition estack :: \<open>('m, 'ch, 'n, 't) ast list \<Rightarrow> (('n, 't) sym \<times> 'ch span list) list\<close> where
  \<open>estack tstk = map (\<lambda>t. (aroot t, aspans t [])) tstk\<close>

text \<open>The error at a stop, given the state number and the remaining input of a
  configuration and the length of the word. The parser fails on the word, so the
  run does not reach a final configuration (\<open>DDone\<close>) and terminates (\<open>None\<close>
  only stands for a run without end); both are reported nonetheless, at the
  final configuration and as a cycle at the start.\<close>

definition dperr :: \<open>('c \<Rightarrow> nat) \<Rightarrow> ('c \<Rightarrow> 'w list) \<Rightarrow> ('w \<Rightarrow> ('t, 'ch, 'm) token_scheme) \<Rightarrow>
    ('c \<Rightarrow> 't list \<times> bool) \<Rightarrow> nat \<Rightarrow> ('c, ('m, 'ch, 'n, 't) ast) dstop option \<Rightarrow>
    ('n, 't, 'ch, 'm) perr\<close> where
  \<open>dperr state inp dec ex n r = (case r of
       None \<Rightarrow> \<lparr>pe_index = 0, pe_tok = None, pe_state = 0, pe_kind = ReduceCycle,
         pe_expected = [], pe_expect_end = False, pe_columns = [], pe_anchor = None,
         pe_shift_state = 0, pe_stack = []\<rparr>
     | Some s \<Rightarrow>
         let (k, st, sh) = (case s of DDone st \<Rightarrow> (NoAction, st, st)
                                   | DStuck k st sh \<Rightarrow> (k, st, sh));
             c = fst st;
             (ts, e) = ex (fst sh)
         in \<lparr>pe_index = n - length (inp c),
            pe_tok = (case inp c of [] \<Rightarrow> None | x # _ \<Rightarrow> Some (dec x)),
            pe_state = state c, pe_kind = k, pe_expected = ts, pe_expect_end = e,
            pe_columns = [], pe_anchor = None, pe_shift_state = state (fst sh),
            pe_stack = estack (snd st)\<rparr>)\<close>

subsection \<open>The layout-free adapter\<close>

text \<open>The step of the simple driver on the plain action table
  (\<^const>\<open>pctl\<close>, \<^const>\<open>pfinal\<close>) over the input numbered by \<^const>\<open>tenc\<close>, started as
  the parser's code equation starts \<^const>\<open>brun\<close>. This is the only place that
  knows the tables.\<close>

definition pstate :: \<open>nat list \<times> 'w list \<Rightarrow> nat\<close> where
  \<open>pstate c = (case fst c of [] \<Rightarrow> 0 | k # _ \<Rightarrow> k)\<close>

definition pdiag_run :: \<open>('n, 't) ptabs \<Rightarrow> nat \<Rightarrow> ('t \<Rightarrow> nat) \<Rightarrow> ('t, 'ch, 'm) token_scheme list \<Rightarrow>
    (nat list \<times> (('t, 'ch, 'm) token_scheme \<times> nat) list, ('m, 'ch, 'n, 't) ast) dstop option\<close> where
  \<open>pdiag_run P i0 f w =
     (let st = (([i0], map (tenc f) w), [])
      in drun_diag (pctl P) (pfinal P) fst snd fst (None, 1, 1) st st)\<close>

text \<open>A trial needs a token of the lookahead's terminal, but stops at its
  shift and never reads it beyond its number; it gets an empty span, so the
  candidates can be terminals and the end of the input needs no token.\<close>

definition ptrial :: \<open>('t \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> 't option \<Rightarrow>
    nat list \<times> (('t, unit) token \<times> nat) list\<close> where
  \<open>ptrial f kstk x = (kstk, case x of None \<Rightarrow> []
     | Some t \<Rightarrow> [tenc f \<lparr>tok = t, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 0, s_txt = []\<rparr>\<rparr>])\<close>

definition pexpect :: \<open>('n, 't) ptabs \<Rightarrow> ('t \<Rightarrow> nat) \<Rightarrow> 't list \<Rightarrow> nat list \<times> 'w \<Rightarrow> 't list \<times> bool\<close> where
  \<open>pexpect P f ts c = dexpect (pctl P) (pfinal P) fst (ptrial f (fst c)) ts\<close>

text \<open>The error of a rejected word, with the terminals \<open>ts\<close> as candidates.\<close>

definition pdiagnose :: \<open>('n, 't) ptabs \<Rightarrow> nat \<Rightarrow> ('t \<Rightarrow> nat) \<Rightarrow> 't list \<Rightarrow>
    ('t, 'ch, 'm) token_scheme list \<Rightarrow> ('n, 't, 'ch, 'm) perr\<close> where
  \<open>pdiagnose P i0 f ts w = dperr pstate snd fst (pexpect P f ts) (length w) (pdiag_run P i0 f w)\<close>

subsection \<open>The set-anchored adapter\<close>

text \<open>The step of the set-anchored driver of the parser's code equation, on the
  control part of a driver state and the depth of its stack: \<^const>\<open>dstep_act\<close>
  for the dense drivers (\<^const>\<open>drun\<^sub>w\<^sub>f\<close>, \<^const>\<open>drun_nh_c\<close>), the step of
  \<^const>\<open>sdrun\<close> for the sparse one. Both keep a stack of closures whose items are
  a production, a dot and an anchor set, and differ only in how they represent
  the production, so the adapter is generic in it (\<open>'p\<close>) and takes the step
  \<open>stp\<close> and the final test \<open>fin\<close>. The closures come from the cache stack, as
  in the parser, so a step computes only the closure of the frame it pushes; the
  AST stack is the engine's. The step keeps the depth, and the loop check
  compares it first, so two configurations of a chain of reductions are told
  apart without walking their stacks. A step is used at two token types, the
  parser's for the run and \<open>unit\<close> for the trials, so the functions below take
  one instance each.\<close>

type_synonym 'p aitem = \<open>'p \<times> nat \<times> indrep\<close>

type_synonym ('p, 't) agconfig = \<open>'p aitem list list \<times> ('t \<times> nat) list\<close>

type_synonym ('m, 'ch, 'p, 'n, 't) ast_st =
  \<open>('p, 't) agconfig \<times> 'p aitem list list \<times> nat list \<times> ('m, 'ch, 't) tword \<times>
   ('m, 'ch, 'n, 't) ast list\<close>

type_synonym ('m, 'ch, 'p, 'n, 't) astep =
  \<open>('m, 'ch, 'p, 'n, 't) ast_st \<Rightarrow> (('n, 't) dact \<times> ('m, 'ch, 'p, 'n, 't) ast_st) option\<close>

type_synonym ('m, 'ch, 'p, 't) lcfg =
  \<open>(('p, 't) agconfig \<times> 'p aitem list list \<times> nat list \<times> ('m, 'ch, 't) tword) \<times> nat\<close>

definition lctl :: \<open>('m, 'ch, 'p, 'n, 't) astep \<Rightarrow>
    ('m, 'ch, 'p, 't) lcfg \<Rightarrow> (('n, 't) dact \<times> ('m, 'ch, 'p, 't) lcfg) option\<close> where
  \<open>lctl stp c = (case c of ((gc, cstk, istk, v), n) \<Rightarrow>
     map_option (\<lambda>(a, (gc', cstk', istk', v', _)). (a, (gc', cstk', istk', v'),
         case a of DShift \<Rightarrow> Suc n | DReduce pr \<Rightarrow> Suc (n - length (snd pr))))
       (stp (gc, cstk, istk, v, [])))\<close>

definition lfin :: \<open>(('p, 't) agconfig \<Rightarrow> bool) \<Rightarrow> ('m, 'ch, 'p, 't) lcfg \<Rightarrow> bool\<close> where
  \<open>lfin fin c = fin (fst (fst c))\<close>

definition lkey :: \<open>('m, 'ch, 'p, 't) lcfg \<Rightarrow>
    (nat \<times> 'p aitem list list \<times> 'p aitem list list \<times> nat list) list\<close> where
  \<open>lkey c = (case c of (((Xs, w), cstk, istk, v), n) \<Rightarrow> [(n, Xs, cstk, istk)])\<close>

definition linp :: \<open>('m, 'ch, 'p, 't) lcfg \<Rightarrow> ('m, 'ch, 't) tword\<close> where
  \<open>linp c = (case c of ((gc, cstk, istk, v), n) \<Rightarrow> v)\<close>

definition lstate :: \<open>('m, 'ch, 'p, 't) lcfg \<Rightarrow> nat\<close> where
  \<open>lstate c = (case c of ((gc, cstk, istk, v), n) \<Rightarrow> (case istk of [] \<Rightarrow> 0 | k # _ \<Rightarrow> k))\<close>

text \<open>The run, started as the code equation starts the driver.\<close>

definition ldiag_run :: \<open>('m, 'ch, 'p, 'n, 't) astep \<Rightarrow> (('p, 't) agconfig \<Rightarrow> bool) \<Rightarrow>
    'p aitem list \<Rightarrow> 'p aitem list \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow>
    (('m, 'ch, 'p, 't) lcfg, ('m, 'ch, 'n, 't) ast) dstop option\<close> where
  \<open>ldiag_run stp fin xin xclos i\<^sub>0 w =
     (let c = ((([xin], tcols w), [xclos], [i\<^sub>0], w), 1)
      in drun_diag (lctl stp) (lfin fin) lkey linp id (None, 1, 1) (c, []) (c, []))\<close>

text \<open>A trial puts a candidate, a terminal at a column, as the only lookahead on
  the saved configuration, into the input of the machine and of the driver
  alike: the former is \<^const>\<open>tcols\<close> of the latter, so the two agree. The token
  is fresh, as in the layout-free adapter, since the end of the input has no
  offending token to change; the step reads only its terminal and its column,
  and the trial stops at its shift.\<close>

definition ltrial :: \<open>('m, 'ch, 'p, 't) lcfg \<Rightarrow> ('t \<times> nat) option \<Rightarrow> (unit, unit, 'p, 't) lcfg\<close> where
  \<open>ltrial c x = (case c of (((Xs, w), cstk, istk, v), n) \<Rightarrow>
     let v' = (case x of None \<Rightarrow> []
       | Some (t, k) \<Rightarrow> [\<lparr>tok = t, span = \<lparr>s_line = 0, s_col = k, s_off = 0, s_len = 0, s_txt = []\<rparr>\<rparr>])
     in (((Xs, tcols v'), cstk, istk, v'), n))\<close>

definition ltry :: \<open>(unit, unit, 'p, 'n, 't) astep \<Rightarrow> (('p, 't) agconfig \<Rightarrow> bool) \<Rightarrow>
    ('m, 'ch, 'p, 't) lcfg \<Rightarrow> ('t \<times> nat) option \<Rightarrow> bool\<close> where
  \<open>ltry stp fin c x = (dtrial (lctl stp) (lfin fin) lkey (None, 1, 1) (ltrial c x) = Some True)\<close>

subsection \<open>Columns\<close>

text \<open>Which columns to try. A step compares the column of the lookahead only
  with anchor sets: those of the frames when it licenses a reduce
  (\<^const>\<open>dlic\<close>, \<^const>\<open>irep_ex_wsat\<close>), and the set it intersects with the
  preimage of the singleton column when it shifts (\<^const>\<open>lgoto\<close>,
  \<^const>\<open>irep_pre\<close>). Each comparison is membership, a bound by the least or the
  greatest element, or by one more or less, so its outcome changes only next to
  the end of a run of consecutive columns in some set. The sets of a trial are
  those of the saved stack and its closures, and those its reductions derive from
  them. So we try \<open>0\<close> and the columns next to the ends of the runs of the sets
  on the saved stack and its closures, and take acceptance as constant between
  two of them. The derived sets are not scanned: that they add no ends is a claim
  checked on the tests against a scan of every column, not proved.\<close>

definition run_ends :: \<open>nat list \<Rightarrow> nat list\<close> where
  \<open>run_ends xs = filter (\<lambda>x. x - 1 \<notin> set xs \<or> Suc x \<notin> set xs) xs\<close>

fun irep_ends :: \<open>indrep \<Rightarrow> nat list\<close> where
  \<open>irep_ends (FinRep xs) = run_ends xs\<close>
| \<open>irep_ends (UpRep xs n) = n # run_ends xs\<close>

text \<open>The columns next to the ends \<open>es\<close>, ascending and distinct: their cost
  follows the number of ends, not how large a column is.\<close>

fun col_ins :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>col_ins x [] = [x]\<close>
| \<open>col_ins x (y # ys) =
     (if x < y then x # y # ys else if x = y then y # ys else y # col_ins x ys)\<close>

definition col_reps :: \<open>nat list \<Rightarrow> nat list\<close> where
  \<open>col_reps es = fold col_ins (concat (map (\<lambda>e. [e - 1, e, Suc e]) es)) [0]\<close>

definition lreps :: \<open>('m, 'ch, 'p, 't) lcfg \<Rightarrow> nat list\<close> where
  \<open>lreps c = (case c of (((Xs, w), cstk, istk, v), n) \<Rightarrow>
     col_reps (concat (map (\<lambda>(pr, m, R). irep_ends R) (concat (Xs @ cstk)))))\<close>

text \<open>The accepted columns as intervals, from the outcomes at the tried columns,
  ascending: two accepted neighbours span the columns between them, and an
  accepted last one every column after it.\<close>

fun cols_of :: \<open>(nat \<times> bool) list \<Rightarrow> colset\<close> where
  \<open>cols_of [] = []\<close>
| \<open>cols_of ((r, False) # rs) = cols_of rs\<close>
| \<open>cols_of ((r, True) # rs) = (case rs of
       [] \<Rightarrow> [(r, None)]
     | (_, True) # _ \<Rightarrow> (case cols_of rs of (_, h) # is \<Rightarrow> (r, h) # is | [] \<Rightarrow> [(r, None)])
     | (_, False) # _ \<Rightarrow> (r, Some r) # cols_of rs)\<close>

definition col_in :: \<open>nat \<Rightarrow> colset \<Rightarrow> bool\<close> where
  \<open>col_in k cs = list_ex (\<lambda>(a, b). a \<le> k \<and> (case b of None \<Rightarrow> True | Some b \<Rightarrow> k \<le> b)) cs\<close>

text \<open>The expected terminals, each with the columns at which it is accepted, and
  whether the end of the input is, from a trial at a terminal and column or at the
  end, the columns \<open>rs\<close> to try and the candidates \<open>ts\<close>.\<close>

definition columns_at :: \<open>(('t \<times> nat) option \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> 't list \<Rightarrow>
    ('t \<times> colset) list \<times> bool\<close> where
  \<open>columns_at try rs ts =
     (filter (\<lambda>(t, cs). cs \<noteq> [])
        (map (\<lambda>t. (t, cols_of (map (\<lambda>r. (r, try (Some (t, r)))) rs))) ts),
      try None)\<close>

definition lcolumns :: \<open>(unit, unit, 'p, 'n, 't) astep \<Rightarrow> (('p, 't) agconfig \<Rightarrow> bool) \<Rightarrow>
    't list \<Rightarrow> ('m, 'ch, 'p, 't) lcfg \<Rightarrow> ('t \<times> colset) list \<times> bool\<close> where
  \<open>lcolumns stp fin ts c = columns_at (ltry stp fin c) (lreps c) ts\<close>

subsection \<open>The anchor\<close>

text \<open>The first token of a tree.\<close>

fun afirst :: \<open>('m, 'ch, 'n, 't) ast \<Rightarrow> ('t, 'ch, 'm) token_scheme option\<close>
  and afirsts :: \<open>('m, 'ch, 'n, 't) ast list \<Rightarrow> ('t, 'ch, 'm) token_scheme option\<close> where
  \<open>afirst (Leaf t) = Some t\<close>
| \<open>afirst (Node n ts) = afirsts ts\<close>
| \<open>afirsts [] = None\<close>
| \<open>afirsts (t # ts) = (case afirst t of None \<Rightarrow> afirsts ts | r \<Rightarrow> r)\<close>

text \<open>An offending token accepted at other columns is placed against the accepted
  column nearest to it. In an interval unbounded to the right that is its start
  \<open>a\<close>, and the token must be indented further than a construct at \<open>a - 1\<close> or as
  far as one at \<open>a\<close> (\<^const>\<open>Offside\<close>); otherwise it must be aligned with one at
  that column (\<^const>\<open>Misaligned\<close>). The construct is the innermost subtree on the
  AST stack after the last shift that starts at such a column, and the anchor is
  its first token. This matches columns, it does not trace which frame's anchor
  set excluded the token: the frames carry sets of columns, not the tokens that
  fixed them.\<close>

definition lanchor :: \<open>nat list \<Rightarrow> ('m, 'ch, 'n, 't) ast list \<Rightarrow> ('t, 'ch, 'm) token_scheme option\<close> where
  \<open>lanchor ks tstk = find (\<lambda>t. s_col (span t) \<in> set ks) (List.map_filter afirst tstk)\<close>

definition lmisplaced :: \<open>nat \<Rightarrow> colset \<Rightarrow> ('m, 'ch, 'n, 't) ast list \<Rightarrow>
    perr_kind \<times> ('t, 'ch, 'm) token_scheme option\<close> where
  \<open>lmisplaced c cl tstk =
     (let near = (\<lambda>(a, b). (case b of None \<Rightarrow> (max a c, True) | Some b \<Rightarrow> (max a (min c b), False)));
          dist = (\<lambda>k. if k \<le> c then c - k else k - c);
          cands = map near cl;
          (k, up) = fold (\<lambda>y x. if dist (fst y) < dist (fst x) then y else x) (tl cands) (hd cands)
      in if up then (Offside cl, lanchor [k - 1, k] tstk) else (Misaligned cl, lanchor [k] tstk))\<close>

subsection \<open>The error\<close>

text \<open>The error at a stop, from its kind, the size \<open>n\<close> of the word, the input left,
  the state at the stop and after the last shift, the columns, and the AST stacks
  after the last shift and at the stop; a token with no action that is accepted at
  another column is \<^const>\<open>Offside\<close> or \<^const>\<open>Misaligned\<close>.\<close>

definition mk_perr :: \<open>perr_kind \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    ('t \<times> colset) list \<times> bool \<Rightarrow> ('m, 'ch, 'n, 't) ast list \<Rightarrow> ('m, 'ch, 'n, 't) ast list \<Rightarrow>
    ('n, 't, 'ch, 'm) perr\<close> where
  \<open>mk_perr k n v st sh ce tstk' tstk =
     (let (cols, e) = ce;
          tk = (case v of [] \<Rightarrow> None | x # _ \<Rightarrow> Some x);
          (k', anc) = (case (k, tk) of
              (NoAction, Some x) \<Rightarrow> (case map_of cols (tok x) of
                  Some cl \<Rightarrow> lmisplaced (s_col (span x)) cl tstk'
                | None \<Rightarrow> (k, None))
            | _ \<Rightarrow> (k, None))
      in \<lparr>pe_index = n - length v, pe_tok = tk, pe_state = st, pe_kind = k',
         pe_expected = map fst cols, pe_expect_end = e, pe_columns = cols, pe_anchor = anc,
         pe_shift_state = sh, pe_stack = estack tstk\<rparr>)\<close>

text \<open>The error at a stop of the set-anchored drivers, with the terminals \<open>ts\<close> as
  candidates.\<close>

definition ldperr :: \<open>(unit, unit, 'p, 'n, 't) astep \<Rightarrow> (('p, 't) agconfig \<Rightarrow> bool) \<Rightarrow>
    't list \<Rightarrow> nat \<Rightarrow> (('m, 'ch, 'p, 't) lcfg, ('m, 'ch, 'n, 't) ast) dstop option \<Rightarrow>
    ('n, 't, 'ch, 'm) perr\<close> where
  \<open>ldperr stp fin ts n r = (case r of
       None \<Rightarrow> dperr lstate linp id (\<lambda>_. ([], False)) n r
     | Some s \<Rightarrow>
         let (k, st, sh) = (case s of DDone st \<Rightarrow> (NoAction, st, st)
                                    | DStuck k st sh \<Rightarrow> (k, st, sh))
         in mk_perr k n (linp (fst st)) (lstate (fst st)) (lstate (fst sh))
              (lcolumns stp fin ts (fst sh)) (snd sh) (snd st))\<close>

text \<open>The error of a word the set-anchored parser rejects: for the dense drivers
  over the tables and the start frame of \<^text>\<open>dparse_via_tables\<close>, for the
  sparse one over the bundle and the start frame of \<^text>\<open>dparse_via_tables_s\<close>.\<close>

definition ldiagnose :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> ('n, 't) xitem list \<Rightarrow>
    ('n, 't) xitem list \<Rightarrow> nat \<Rightarrow> 't list \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> ('n, 't, 'ch, 'm) perr\<close> where
  \<open>ldiagnose G Shn gt sts redtab xin xclos i\<^sub>0 ts w =
     ldperr (dstep_act G gt sts redtab) (gfinal G Shn) ts (length w)
       (ldiag_run (dstep_act G gt sts redtab) (gfinal G Shn) xin xclos i\<^sub>0 w)\<close>

definition sdstep_dact :: \<open>('n, 't) stab \<Rightarrow> ('m, 'ch, 'n, 't) sdst \<Rightarrow>
    (('n, 't) dact \<times> ('m, 'ch, 'n, 't) sdst) option\<close> where
  \<open>sdstep_dact T st = map_option (\<lambda>(a, st'). (sdec_act a, st')) (sdstep_act T st)\<close>

definition sdiagnose :: \<open>('n, 't) stab \<Rightarrow> ('n, 't) sitem list \<Rightarrow> ('n, 't) sitem list \<Rightarrow>
    nat \<Rightarrow> 't list \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> ('n, 't, 'ch, 'm) perr\<close> where
  \<open>sdiagnose T kin kcl i\<^sub>0 ts w =
     ldperr (sdstep_dact T) (sgfinal T) ts (length w)
       (ldiag_run (sdstep_dact T) (sgfinal T) kin kcl i\<^sub>0 w)\<close>

section \<open>One pass\<close>

text \<open>The diagnoses above run a rejected word a second time. Here the run that
  decides acceptance keeps what the error needs, so every word is run once: an
  accepted word gives the parser's tree, a rejected one the error where the run
  stopped. The run takes the parser's step unchanged and adds only the
  configuration after the last shift, one argument more, so an accepted word costs
  what the parser costs. For the simple driver that run is \<^const>\<open>drun_diag\<close>,
  whose loop check is \<^const>\<open>brun\<close>'s. The set-anchored drivers without a history
  have no loop check, and their run, \<open>arun\<close>, has none either. Only the
  accepted words are proved: the one pass returns a tree exactly when the
  parser does, and the same tree (the \<open>Inr_iff\<close> facts below).\<close>

subsection \<open>The simple driver\<close>

fun dstop_tree :: \<open>('c, ('m, 'ch, 'n, 't) ast) dstop \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close> where
  \<open>dstop_tree (DDone st) = sresult (snd st)\<close>
| \<open>dstop_tree (DStuck k st sh) = None\<close>

lemma brun_imp_drun_diag:
  assumes \<open>brun ctl fin dec d st = Some t\<close>
  shows \<open>\<forall>sh. Option.bind (drun_diag ctl fin fst snd dec d sh ((fst st, fst (snd st)), snd (snd st)))
           dstop_tree = Some t\<close>
proof (rule brun.raw_induct[OF _ assms], goal_cases)
  case (1 f ctl fin dec d st t)
  obtain stk v tstk where st: \<open>st = (stk, v, tstk)\<close> by (cases st)
  show ?case
  proof (cases \<open>fin (stk, v)\<close>)
    case True
    with "1"(2) show ?thesis unfolding st by (simp add: drun_diag.simps)
  next
    case False
    with "1"(2) obtain act stk' v' where nc: \<open>fst d \<noteq> Some stk\<close>
        and c: \<open>ctl (stk, v) = Some (act, stk', v')\<close>
        and r: \<open>f ctl fin dec (if act = DShift then (None, 1, 1) else bupd d stk)
                 (stk', v', xtree dec act v tstk) = Some t\<close>
      unfolding st by (auto simp: bind_eq_Some_conv split: if_splits)
    from "1"(1)[OF r] have IH: \<open>\<forall>sh. Option.bind (drun_diag ctl fin fst snd dec
        (if act = DShift then (None, 1, 1) else bupd d stk) sh ((stk', v'), xtree dec act v tstk))
        dstop_tree = Some t\<close>
      by simp
    show ?thesis
    proof
      fix sh
      show \<open>Option.bind (drun_diag ctl fin fst snd dec d sh ((fst st, fst (snd st)), snd (snd st)))
          dstop_tree = Some t\<close>
        using False nc c IH[THEN spec[where x = sh]]
          IH[THEN spec[where x = \<open>((stk', v'), xtree dec act v tstk)\<close>]] unfolding st
        by (subst drun_diag.simps) (cases \<open>act = DShift\<close>; simp add: Let_def)    qed
  qed
qed

lemma drun_diag_imp_brun:
  assumes \<open>drun_diag ctl fin key inp dec d sh st = Some r\<close>
  shows \<open>key = fst \<longrightarrow> inp = snd \<longrightarrow> (\<forall>t. dstop_tree r = Some t \<longrightarrow>
           brun ctl fin dec d (fst (fst st), snd (fst st), snd st) = Some t)\<close>
proof (rule drun_diag.raw_induct[OF _ assms], goal_cases)
  case (1 f ctl fin key inp dec d sh st r)
  obtain stk v tstk where st: \<open>st = ((stk, v), tstk)\<close> by (cases st) auto
  show ?case
  proof (intro impI allI)
    fix t
    assume k: \<open>key = fst\<close> and i: \<open>inp = snd\<close> and t: \<open>dstop_tree r = Some t\<close>
    show \<open>brun ctl fin dec d (fst (fst st), snd (fst st), snd st) = Some t\<close>
    proof (cases \<open>fin (stk, v)\<close>)
      case True
      with "1"(2) t show ?thesis unfolding st by (subst brun.simps) auto
    next
      case False
      show ?thesis
      proof (cases \<open>fst d = Some stk\<close>)
        case True
        with False "1"(2) t show ?thesis unfolding st k by auto
      next
        case nc: False
        show ?thesis
        proof (cases \<open>ctl (stk, v)\<close>)
          case None
          with False nc "1"(2) t show ?thesis unfolding st k by auto
        next
          case (Some p)
          then obtain act stk' v' where c: \<open>ctl (stk, v) = Some (act, stk', v')\<close>
            by (cases p) auto
          from False nc c "1"(2) obtain sh' where
              rec: \<open>f ctl fin key inp dec (if act = DShift then (None, 1, 1) else bupd d stk) sh'
                     ((stk', v'), xtree dec act v tstk) = Some r\<close>
            unfolding st k i by (cases \<open>act = DShift\<close>) (auto simp: Let_def)
          from "1"(1)[OF rec] k i t have
              \<open>brun ctl fin dec (if act = DShift then (None, 1, 1) else bupd d stk)
                 (stk', v', xtree dec act v tstk) = Some t\<close>
            by simp
          with False nc c show ?thesis unfolding st by (subst brun.simps) simp
        qed
      qed
    qed
  qed
qed

text \<open>The parser's run and the diagnosing run, from any saved configuration.\<close>

lemma brun_drun_diag:
  \<open>brun ctl fin dec d (stk, v, tstk) =
     Option.bind (drun_diag ctl fin fst snd dec d sh ((stk, v), tstk)) dstop_tree\<close>
proof (cases \<open>brun ctl fin dec d (stk, v, tstk)\<close>)
  case None
  show ?thesis
  proof (cases \<open>drun_diag ctl fin fst snd dec d sh ((stk, v), tstk)\<close>)
    case (Some r)
    show ?thesis
    proof (cases \<open>dstop_tree r\<close>)
      case (Some t)
      from drun_diag_imp_brun[OF \<open>drun_diag _ _ _ _ _ _ _ _ = Some r\<close>] Some None show ?thesis
        by simp
    qed (simp add: None \<open>drun_diag _ _ _ _ _ _ _ _ = Some r\<close>)
  qed (simp add: None)
next
  case (Some t)
  with brun_imp_drun_diag[OF Some, THEN spec[where x = sh]] show ?thesis by simp
qed

text \<open>The one pass of the simple driver: the tree decoded by \<open>dec\<close>, or the error
  of \<^const>\<open>pdiagnose\<close>, from the same run.\<close>

definition pdiag :: \<open>('n, 't) ptabs \<Rightarrow> nat \<Rightarrow> ('t \<Rightarrow> nat) \<Rightarrow> 't list \<Rightarrow>
    (('m, 'ch, 'n, 't) ast \<Rightarrow> 'x option) \<Rightarrow> ('t, 'ch, 'm) token_scheme list \<Rightarrow>
    ('n, 't, 'ch, 'm) perr + 'x\<close> where
  \<open>pdiag P i0 f ts dec w =
     (let r = pdiag_run P i0 f w
      in case Option.bind (Option.bind r dstop_tree) dec of
           Some x \<Rightarrow> Inr x
         | None \<Rightarrow> Inl (dperr pstate snd fst (pexpect P f ts) (length w) r))\<close>

lemma pdiag_Inr_iff:
  \<open>pdiag P i0 f ts dec w = Inr x \<longleftrightarrow>
     Option.bind (brun (pctl P) (pfinal P) fst (None, 1, 1) ([i0], map (tenc f) w, [])) dec = Some x\<close>
  unfolding pdiag_def pdiag_run_def Let_def brun_drun_diag[where sh = \<open>(([i0], map (tenc f) w), [])\<close>]
  by (simp add: Let_def split: option.split)

subsection \<open>The set-anchored drivers\<close>

text \<open>The run stops at a final configuration (\<open>ADone\<close>) or where the step has no
  action (\<open>AStuck\<close>, with the configuration after the last shift).\<close>

datatype 's astop = ADone 's | AStuck 's 's

partial_function (option) arun ::
  \<open>('s \<Rightarrow> ('a \<times> 's) option) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's astop option\<close>
  where
  \<open>arun stp sft fin sh st =
     (if fin st then Some (ADone st)
      else (case stp st of
        None \<Rightarrow> Some (AStuck st sh)
      | Some (a, st') \<Rightarrow> arun stp sft fin (if sft a then st' else sh) st'))\<close>

lemmas arun_simps [code] = arun.simps

fun is_dshift :: \<open>('n, 't) dact \<Rightarrow> bool\<close> where
  \<open>is_dshift DShift = True\<close>
| \<open>is_dshift (DReduce pr) = False\<close>

fun is_sshift :: \<open>('n, 't) sact \<Rightarrow> bool\<close> where
  \<open>is_sshift SShift = True\<close>
| \<open>is_sshift (SReduce r) = False\<close>

definition dst_tree :: \<open>'g \<times> 'c \<times> 'i \<times> 'v \<times> ('m, 'ch, 'n, 't) ast list \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close> where
  \<open>dst_tree st = (case st of (gc, cstk, istk, v, tstk) \<Rightarrow> sresult tstk)\<close>

fun astop_tree :: \<open>('g \<times> 'c \<times> 'i \<times> 'v \<times> ('m, 'ch, 'n, 't) ast list) astop \<Rightarrow>
    ('m, 'ch, 'n, 't) ast option\<close> where
  \<open>astop_tree (ADone st) = dst_tree st\<close>
| \<open>astop_tree (AStuck st sh) = None\<close>

text \<open>A driver that runs \<open>stp\<close> until \<open>fin\<close> holds, given by its unfolding \<open>eq\<close>,
  returns the tree of every final configuration the run reaches.\<close>

lemma arun_imp:
  assumes r: \<open>arun stp sft fin sh st = Some r\<close>
    and eq: \<open>\<And>st. F st = (if fin st then dst_tree st else Option.bind (map_option snd (stp st)) F)\<close>
  shows \<open>\<forall>t. astop_tree r = Some t \<longrightarrow> F st = Some t\<close>
proof -
  have \<open>stp' = stp \<longrightarrow> fin' = fin \<longrightarrow> (\<forall>t. astop_tree r = Some t \<longrightarrow> F st = Some t)\<close>
    if \<open>arun stp' sft fin' sh st = Some r\<close> for stp' fin'
  proof (rule arun.raw_induct[OF _ that], goal_cases)
    case (1 f stp' sft fin' sh st r)
    show ?case
    proof (intro impI allI)
      fix t
      assume s: \<open>stp' = stp\<close> and fi: \<open>fin' = fin\<close> and t: \<open>astop_tree r = Some t\<close>
      show \<open>F st = Some t\<close>
      proof (cases \<open>fin st\<close>)
        case True
        with "1"(2) t s fi show ?thesis by (subst eq) auto
      next
        case False
        show ?thesis
        proof (cases \<open>stp st\<close>)
          case None
          with False "1"(2) t s fi show ?thesis by auto
        next
          case (Some p)
          then obtain a st' where p: \<open>stp st = Some (a, st')\<close> by (cases p) auto
          with False "1"(2) s fi have rec: \<open>f stp' sft fin' (if sft a then st' else sh) st' = Some r\<close>
            by simp
          from "1"(1)[OF rec] s fi t have \<open>F st' = Some t\<close> by simp
          with False p show ?thesis by (subst eq) simp
        qed
      qed
    qed
  qed
  with r show ?thesis by simp
qed

lemma arun_fin: \<open>fin st \<Longrightarrow> arun stp sft fin sh st = Some (ADone st)\<close>
  by (subst arun.simps) simp

lemma arun_step:
  \<open>\<not> fin st \<Longrightarrow> stp st = Some (a, st') \<Longrightarrow>
     arun stp sft fin sh st = arun stp sft fin (if sft a then st' else sh) st'\<close>
  by (subst arun.simps) simp

text \<open>The two drivers, each as a run of \<^const>\<open>arun\<close> from any saved
  configuration.\<close>

lemma dstep_c_act_c: \<open>dstep_c G gt sts redtab dt st = map_option snd (dstep_act_c G gt sts redtab dt st)\<close>
  unfolding dstep_c_def dstep_act_c_def
  by (auto simp: Let_def split: prod.splits option.splits dact.splits)

lemma drun_nh_c_eq:
  \<open>drun_nh_c G Shn gt sts redtab dt st =
     (if gfinal G Shn (fst st) then dst_tree st
      else Option.bind (map_option snd (dstep_act_c G gt sts redtab dt st)) (drun_nh_c G Shn gt sts redtab dt))\<close>
  by (subst drun_nh_c.simps) (auto simp: dst_tree_def sresult_def dstep_c_act_c split: prod.splits list.splits)

lemma drun_nh_c_imp_arun:
  assumes \<open>drun_nh_c G Shn gt sts redtab dt st = Some t\<close>
  shows \<open>\<forall>sh. Option.bind (arun (dstep_act_c G gt sts redtab dt) is_dshift (\<lambda>s. gfinal G Shn (fst s)) sh st)
           astop_tree = Some t\<close>
proof (rule drun_nh_c.raw_induct[OF _ assms], goal_cases)
  case (1 f G Shn gt sts redtab dt st t)
  show ?case
  proof (cases \<open>gfinal G Shn (fst st)\<close>)
    case True
    with "1"(2) show ?thesis
      by (cases st) (auto simp: arun_fin dst_tree_def sresult_def split: list.splits)
  next
    case False
    with "1"(2) obtain a st' where s: \<open>dstep_act_c G gt sts redtab dt st = Some (a, st')\<close>
        and rec: \<open>f G Shn gt sts redtab dt st' = Some t\<close>
      by (cases st) (auto simp: bind_eq_Some_conv dstep_c_act_c)
    show ?thesis
    proof
      fix sh
      from "1"(1)[OF rec, THEN spec[where x = \<open>if is_dshift a then st' else sh\<close>]] False s
      show \<open>Option.bind (arun (dstep_act_c G gt sts redtab dt) is_dshift (\<lambda>s. gfinal G Shn (fst s)) sh st)
          astop_tree = Some t\<close>
        by (simp add: arun_step)
    qed
  qed
qed

lemma drun_nh_c_arun:
  \<open>drun_nh_c G Shn gt sts redtab dt st =
     Option.bind (arun (dstep_act_c G gt sts redtab dt) is_dshift (\<lambda>s. gfinal G Shn (fst s)) sh st)
       astop_tree\<close>
proof (cases \<open>drun_nh_c G Shn gt sts redtab dt st\<close>)
  case None
  show ?thesis
  proof (cases \<open>arun (dstep_act_c G gt sts redtab dt) is_dshift (\<lambda>s. gfinal G Shn (fst s)) sh st\<close>)
    case (Some r)
    show ?thesis
    proof (cases \<open>astop_tree r\<close>)
      case (Some t)
      from arun_imp[OF \<open>arun _ _ _ _ _ = Some r\<close> drun_nh_c_eq] Some None show ?thesis by simp
    qed (simp add: None \<open>arun _ _ _ _ _ = Some r\<close>)
  qed (simp add: None)
next
  case (Some t)
  with drun_nh_c_imp_arun[OF Some, THEN spec[where x = sh]] show ?thesis by simp
qed

lemma sdrun_eq:
  \<open>sdrun T st =
     (if sgfinal T (fst st) then dst_tree st
      else Option.bind (map_option snd (sdstep_act T st)) (sdrun T))\<close>
  by (subst sdrun.simps) (auto simp: dst_tree_def sresult_def sdstep_def split: prod.splits list.splits)

lemma sdrun_imp_arun:
  assumes \<open>sdrun T st = Some t\<close>
  shows \<open>\<forall>sh. Option.bind (arun (sdstep_act T) is_sshift (\<lambda>s. sgfinal T (fst s)) sh st) astop_tree = Some t\<close>
proof (rule sdrun.raw_induct[OF _ assms], goal_cases)
  case (1 f T st t)
  show ?case
  proof (cases \<open>sgfinal T (fst st)\<close>)
    case True
    with "1"(2) show ?thesis
      by (cases st) (auto simp: arun_fin dst_tree_def sresult_def split: list.splits)
  next
    case False
    with "1"(2) obtain a st' where s: \<open>sdstep_act T st = Some (a, st')\<close> and rec: \<open>f T st' = Some t\<close>
      by (cases st) (auto simp: bind_eq_Some_conv sdstep_def)
    show ?thesis
    proof
      fix sh
      from "1"(1)[OF rec, THEN spec[where x = \<open>if is_sshift a then st' else sh\<close>]] False s
      show \<open>Option.bind (arun (sdstep_act T) is_sshift (\<lambda>s. sgfinal T (fst s)) sh st) astop_tree = Some t\<close>
        by (simp add: arun_step)
    qed
  qed
qed

lemma sdrun_arun:
  \<open>sdrun T st = Option.bind (arun (sdstep_act T) is_sshift (\<lambda>s. sgfinal T (fst s)) sh st) astop_tree\<close>
proof (cases \<open>sdrun T st\<close>)
  case None
  show ?thesis
  proof (cases \<open>arun (sdstep_act T) is_sshift (\<lambda>s. sgfinal T (fst s)) sh st\<close>)
    case (Some r)
    show ?thesis
    proof (cases \<open>astop_tree r\<close>)
      case (Some t)
      from arun_imp[OF \<open>arun _ _ _ _ _ = Some r\<close> sdrun_eq] Some None show ?thesis by simp
    qed (simp add: None \<open>arun _ _ _ _ _ = Some r\<close>)
  qed (simp add: None)next
  case (Some t)
  with sdrun_imp_arun[OF Some, THEN spec[where x = sh]] show ?thesis by simp
qed

text \<open>The error at a stop of \<^const>\<open>arun\<close>, by \<^const>\<open>ldperr\<close> on the
  configurations of \<^const>\<open>lctl\<close>, whose depth is that of the state stack, and the
  one pass of a set-anchored driver: \<open>stp\<close> is its step at the token type of the
  trials, \<open>r\<close> its run.\<close>

definition lcfg_of :: \<open>('m, 'ch, 'p, 'n, 't) ast_st \<Rightarrow> ('m, 'ch, 'p, 't) lcfg \<times> ('m, 'ch, 'n, 't) ast list\<close> where
  \<open>lcfg_of st = (case st of (gc, cstk, istk, v, tstk) \<Rightarrow> (((gc, cstk, istk, v), length istk), tstk))\<close>

fun astop_dstop :: \<open>('m, 'ch, 'p, 'n, 't) ast_st astop \<Rightarrow>
    (('m, 'ch, 'p, 't) lcfg, ('m, 'ch, 'n, 't) ast) dstop\<close> where
  \<open>astop_dstop (ADone st) = DDone (lcfg_of st)\<close>
| \<open>astop_dstop (AStuck st sh) = DStuck NoAction (lcfg_of st) (lcfg_of sh)\<close>

definition adiag :: \<open>(unit, unit, 'p, 'n, 't) astep \<Rightarrow> (('p, 't) agconfig \<Rightarrow> bool) \<Rightarrow> 't list \<Rightarrow>
    (('m, 'ch, 'n, 't) ast \<Rightarrow> 'x option) \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 'p, 'n, 't) ast_st astop option \<Rightarrow>
    ('n, 't, 'ch, 'm) perr + 'x\<close> where
  \<open>adiag stp fin ts dec n r =
     (case Option.bind (Option.bind r astop_tree) dec of
        Some x \<Rightarrow> Inr x
      | None \<Rightarrow> Inl (ldperr stp fin ts n (map_option astop_dstop r)))\<close>

lemma adiag_Inr_iff: \<open>adiag stp fin ts dec n r = Inr x \<longleftrightarrow> Option.bind (Option.bind r astop_tree) dec = Some x\<close>
  unfolding adiag_def by (simp split: option.split)

text \<open>The dense driver \<^const>\<open>drun_nh_c\<close> over the tables and the start frame of
  \<^text>\<open>dparse_via_tables_nh_c\<close>, its trials on the same step.\<close>

definition ldiag_c :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> (nat \<times> nat option) list \<Rightarrow>
    ('n, 't) xitem list \<Rightarrow> ('n, 't) xitem list \<Rightarrow> nat \<Rightarrow> 't list \<Rightarrow>
    (('m, 'ch, 'n, 't) ast \<Rightarrow> 'x option) \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> ('n, 't, 'ch, 'm) perr + 'x\<close> where
  \<open>ldiag_c G Shn gt sts redtab dt xin xclos i\<^sub>0 ts dec w =
     (let st = (([xin], tcols w), [xclos], [i\<^sub>0], w, [])
      in adiag (dstep_act_c G gt sts redtab dt) (gfinal G Shn) ts dec (length w)
           (arun (dstep_act_c G gt sts redtab dt) is_dshift (\<lambda>s. gfinal G Shn (fst s)) st st))\<close>

lemma ldiag_c_Inr_iff:
  \<open>ldiag_c G Shn gt sts redtab dt xin xclos i\<^sub>0 ts dec w = Inr x \<longleftrightarrow>
     Option.bind (drun_nh_c G Shn gt sts redtab dt (([xin], tcols w), [xclos], [i\<^sub>0], w, [])) dec = Some x\<close>
  unfolding ldiag_c_def Let_def adiag_Inr_iff
    drun_nh_c_arun[where sh = \<open>(([xin], tcols w), [xclos], [i\<^sub>0], w, [])\<close>] ..

text \<open>The sparse driver \<^const>\<open>sdrun\<close> over the bundle and the start frame of
  \<^text>\<open>dparse_via_tables_s\<close>.\<close>

definition sdiag :: \<open>('n, 't) stab \<Rightarrow> ('n, 't) sitem list \<Rightarrow> ('n, 't) sitem list \<Rightarrow> nat \<Rightarrow> 't list \<Rightarrow>
    (('m, 'ch, 'n, 't) ast \<Rightarrow> 'x option) \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> ('n, 't, 'ch, 'm) perr + 'x\<close> where
  \<open>sdiag T kin kcl i\<^sub>0 ts dec w =
     (let st = (([kin], tcols w), [kcl], [i\<^sub>0], w, [])
      in adiag (sdstep_dact T) (sgfinal T) ts dec (length w)
           (arun (sdstep_act T) is_sshift (\<lambda>s. sgfinal T (fst s)) st st))\<close>

lemma sdiag_Inr_iff:
  \<open>sdiag T kin kcl i\<^sub>0 ts dec w = Inr x \<longleftrightarrow>
     Option.bind (sdrun T (([kin], tcols w), [kcl], [i\<^sub>0], w, [])) dec = Some x\<close>
  unfolding sdiag_def Let_def adiag_Inr_iff
    sdrun_arun[where sh = \<open>(([kin], tcols w), [kcl], [i\<^sub>0], w, [])\<close>] ..

subsection \<open>The vector driver\<close>

text \<open>The parser's code equation runs \<^const>\<open>vrun_un\<close>. Its one pass keeps the
  configuration after the last shift and tells apart the three ways to stop: at
  a final configuration, where nothing is live, and at a conflict between live
  reductions. Only the last restarts, as the parser does, on the sparse driver:
  a rejected word is reported from the frames where the run stopped. The run has
  no loop check, like \<^const>\<open>vrun_un\<close>, which only runs on grammars without a
  nullable cycle.\<close>

datatype ('m, 'ch, 'n, 't) vstop =
    VConflict
  | VDone \<open>('m, 'ch, 'n, 't) vst_n\<close>
  | VStuck \<open>('m, 'ch, 'n, 't) vst_n\<close> \<open>('m, 'ch, 'n, 't) vst_n\<close>

definition vstep_a :: \<open>('n, 't) vtab \<Rightarrow> ('m, 'ch, 'n, 't) vst_n \<Rightarrow>
    (('n, 't) vact \<times> ('m, 'ch, 'n, 't) vst_n) option option\<close> where
  \<open>vstep_a V st = (case st of (fs, w, v, tstk) \<Rightarrow> (case fs of [] \<Rightarrow> Some None | (j, av) # _ \<Rightarrow>
     (case vchoose_n V (fs, w) (vcands_n V j av w) of None \<Rightarrow> None | Some None \<Rightarrow> Some None
      | Some (Some (act, fs', w')) \<Rightarrow>
          (case tstep (vdec act) (v, tstk) of (v', tstk') \<Rightarrow> Some (Some (act, fs', w', v', tstk'))))))\<close>

partial_function (option) vdrun ::
  \<open>('n, 't) vtab \<Rightarrow> ('m, 'ch, 'n, 't) vst_n \<Rightarrow> ('m, 'ch, 'n, 't) vst_n \<Rightarrow>
    ('m, 'ch, 'n, 't) vstop option\<close>
  where
  \<open>vdrun V sh st =
     (if vfinal_n V st then Some (VDone st)
      else (case vstep_a V st of
        None \<Rightarrow> Some VConflict
      | Some None \<Rightarrow> Some (VStuck st sh)
      | Some (Some (a, st')) \<Rightarrow> vdrun V (case a of VShift \<Rightarrow> st' | VReduce _ _ _ \<Rightarrow> sh) st'))\<close>

lemmas vdrun_simps [code] = vdrun.simps

fun vtree :: \<open>('m, 'ch, 'n, 't) vst_n \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close> where
  \<open>vtree (fs, w, v, tstk) = (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)\<close>

fun vres :: \<open>('m, 'ch, 'n, 't) vstop \<Rightarrow> ('m, 'ch, 'n, 't) ast option option\<close> where
  \<open>vres VConflict = None\<close>
| \<open>vres (VDone st) = Some (vtree st)\<close>
| \<open>vres (VStuck st sh) = Some None\<close>

lemma vstep_un_a: \<open>vstep_un V st = map_option (map_option snd) (vstep_a V st)\<close>
  by (auto simp: vstep_un_def vstep_a_def split: prod.split list.split option.split)

lemma vrun_un_imp_vdrun:
  assumes \<open>vrun_un V st = Some r\<close>
  shows \<open>\<forall>sh. Option.bind (vdrun V sh st) vres = Some r\<close>
proof (rule vrun_un.raw_induct[OF _ assms], goal_cases)
  case (1 f V st r)
  obtain fs w v tstk where st: \<open>st = (fs, w, v, tstk)\<close> by (cases st)
  note body = "1"(2)[unfolded st prod.case, folded st, unfolded vstep_un_a]
  show ?case
  proof
    fix sh
    show \<open>Option.bind (vdrun V sh st) vres = Some r\<close>
    proof (cases \<open>vfinal_n V st\<close>)
      case True
      with body show ?thesis by (subst vdrun.simps) (simp add: st)
    next
      case False
      show ?thesis
      proof (cases \<open>vstep_a V st\<close>)
        case None
        with False body show ?thesis by simp
      next
        case (Some y)
        show ?thesis
        proof (cases y)
          case None
          with \<open>vstep_a V st = Some y\<close> False body show ?thesis by (subst vdrun.simps) simp
        next
          case (Some p)
          obtain a st' where p: \<open>p = (a, st')\<close> by (cases p)
          with \<open>vstep_a V st = Some y\<close> Some False body have \<open>f V st' = Some r\<close> by simp
          from "1"(1)[OF this, THEN spec[where x = \<open>case a of VShift \<Rightarrow> st' | VReduce _ _ _ \<Rightarrow> sh\<close>]]
            \<open>vstep_a V st = Some y\<close> Some p False show ?thesis
            by (subst vdrun.simps) simp
        qed
      qed
    qed
  qed
qed

lemma vdrun_imp_vrun_un:
  assumes \<open>vdrun V sh st = Some s\<close>
  shows \<open>\<forall>r. vres s = Some r \<longrightarrow> vrun_un V st = Some r\<close>
proof (rule vdrun.raw_induct[OF _ assms], goal_cases)
  case (1 f V sh st s)
  obtain fs w v tstk where st: \<open>st = (fs, w, v, tstk)\<close> by (cases st)
  show ?case
  proof (intro allI impI)
    fix r
    assume r: \<open>vres s = Some r\<close>
    show \<open>vrun_un V st = Some r\<close>
    proof (cases \<open>vfinal_n V st\<close>)
      case True
      with "1"(2) r show ?thesis by (subst vrun_un.simps) (auto simp: st)
    next
      case False
      show ?thesis
      proof (cases \<open>vstep_a V st\<close>)
        case None
        with False "1"(2) r show ?thesis by auto
      next
        case (Some y)
        show ?thesis
        proof (cases y)
          case None
          with \<open>vstep_a V st = Some y\<close> False "1"(2) r show ?thesis
            by (subst vrun_un.simps) (auto simp: st vstep_un_a)
        next
          case (Some p)
          obtain a st' where p: \<open>p = (a, st')\<close> by (cases p)
          with \<open>vstep_a V st = Some y\<close> Some False "1"(2)
          have \<open>f V (case a of VShift \<Rightarrow> st' | VReduce _ _ _ \<Rightarrow> sh) st' = Some s\<close> by simp
          from "1"(1)[OF this] r have \<open>vrun_un V st' = Some r\<close> by blast
          moreover from \<open>vstep_a V st = Some y\<close> Some p have \<open>vstep_un V st = Some (Some st')\<close>
            by (simp add: vstep_un_a)
          ultimately show ?thesis using False
            by (subst vrun_un.simps) (simp split: prod.split)
        qed
      qed
    qed
  qed
qed

lemma vrun_un_vdrun: \<open>vrun_un V st = Option.bind (vdrun V sh st) vres\<close>
proof (cases \<open>vrun_un V st\<close>)
  case None
  show ?thesis
  proof (cases \<open>Option.bind (vdrun V sh st) vres\<close>)
    case (Some r)
    then obtain s where \<open>vdrun V sh st = Some s\<close> \<open>vres s = Some r\<close>
      by (auto simp: bind_eq_Some_conv)
    with vdrun_imp_vrun_un None show ?thesis by fastforce
  qed (simp add: None)
next
  case (Some r)
  with vrun_un_imp_vdrun[OF Some, THEN spec[where x = sh]] show ?thesis by simp
qed

text \<open>A trial on the frames after the last shift, as in \<^const>\<open>dtrial\<close>; where two
  reductions are live it takes the first, so the expected terminals are read
  off the run at hand whichever conflict a candidate would meet. It needs
  neither tokens nor trees.\<close>

type_synonym vcfg = \<open>vframes \<times> (nat \<times> nat) list\<close>

fun vpick_n :: \<open>('n, 't) vtab \<Rightarrow> vcfg \<Rightarrow> ('n, 't) vact list \<Rightarrow> (('n, 't) vact \<times> vcfg) option\<close> where
  \<open>vpick_n V c [] = None\<close>
| \<open>vpick_n V c (a # acts) = (case vmstep_n V c a of Some r \<Rightarrow> Some (a, r) | None \<Rightarrow> vpick_n V c acts)\<close>

definition vfin_c :: \<open>('n, 't) vtab \<Rightarrow> vcfg \<Rightarrow> bool\<close> where
  \<open>vfin_c V c = vfinal_n V
     (fst c, snd c, [] :: (unit, unit, 't) tword, [] :: (unit, unit, 'n, 't) ast list)\<close>

partial_function (option) vtrial :: \<open>('n, 't) vtab \<Rightarrow> vcfg \<Rightarrow> bool option\<close> where
  \<open>vtrial V c =
     (if vfin_c V c then Some True
      else (case c of (fs, w) \<Rightarrow> (case fs of [] \<Rightarrow> Some False | (j, av) # _ \<Rightarrow>
        (case vpick_n V c (vcands_n V j av w) of
          None \<Rightarrow> Some False
        | Some (a, c') \<Rightarrow> (case a of VShift \<Rightarrow> Some True | VReduce _ _ _ \<Rightarrow> vtrial V c')))))\<close>

lemmas vtrial_simps [code] = vtrial.simps

definition vtry :: \<open>('n, 't) vtab \<Rightarrow> vcfg \<Rightarrow> ('t \<times> nat) option \<Rightarrow> bool\<close> where
  \<open>vtry V c x = (vtrial V (fst c, case x of None \<Rightarrow> [] | Some (t, k) \<Rightarrow> [(vnum V t, k)]) = Some True)\<close>

text \<open>The columns to try are those of \<^const>\<open>lreps\<close>, from the anchor sets of the
  frames.\<close>

definition vcolumns :: \<open>('n, 't) vtab \<Rightarrow> 't list \<Rightarrow> vcfg \<Rightarrow> ('t \<times> colset) list \<times> bool\<close> where
  \<open>vcolumns V ts c = columns_at (vtry V c)
     (col_reps (concat (map (\<lambda>(j, av). concat (map irep_ends av)) (fst c)))) ts\<close>

definition vtop :: \<open>vframes \<Rightarrow> nat\<close> where
  \<open>vtop fs = (case fs of [] \<Rightarrow> 0 | (j, _) # _ \<Rightarrow> j)\<close>

text \<open>The error at a stop, as \<^const>\<open>ldperr\<close> gives it.\<close>

definition vperr :: \<open>('n, 't) vtab \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 'n, 't) vst_n \<Rightarrow>
    ('m, 'ch, 'n, 't) vst_n \<Rightarrow> ('n, 't, 'ch, 'm) perr\<close> where
  \<open>vperr V ts n st sh = (case (st, sh) of ((fs, _, v, tstk), (fs', w', _, tstk')) \<Rightarrow>
     mk_perr NoAction n v (vtop fs) (vtop fs') (vcolumns V ts (fs', w')) tstk' tstk)\<close>

text \<open>The one pass over the parser's code equation
  \<^text>\<open>dparse_via_tables_vun\<close>.\<close>

definition vdiag :: \<open>('n, 't) vtab \<Rightarrow> ('n, 't) stab \<Rightarrow> ('n, 't) sitem list \<Rightarrow> ('n, 't) sitem list \<Rightarrow>
    nat \<Rightarrow> 't list \<Rightarrow> (('m, 'ch, 'n, 't) ast \<Rightarrow> 'x option) \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow>
    ('n, 't, 'ch, 'm) perr + 'x\<close> where
  \<open>vdiag V T kin kcl i\<^sub>0 ts dec w =
     (let st = ([v_av0 V], vtcols V w, w, [])
      in (case vdrun V st st of
            Some (VDone s) \<Rightarrow> (case Option.bind (vtree s) dec of
                Some x \<Rightarrow> Inr x
              | None \<Rightarrow> Inl (vperr V ts (length w) s s))
          | Some (VStuck s sh) \<Rightarrow> Inl (vperr V ts (length w) s sh)
          | _ \<Rightarrow> sdiag T kin kcl i\<^sub>0 ts dec w))\<close>

lemma vdiag_Inr_iff:
  \<open>vdiag V T kin kcl i\<^sub>0 ts dec w = Inr x \<longleftrightarrow>
     Option.bind (case vrun_un V ([v_av0 V], vtcols V w, w, []) of
         Some r \<Rightarrow> r | None \<Rightarrow> sdrun T (([kin], tcols w), [kcl], [i\<^sub>0], w, [])) dec = Some x\<close>
  unfolding vdiag_def Let_def
    vrun_un_vdrun[where sh = \<open>([v_av0 V], vtcols V w, w, [])\<close>]
  by (auto simp: sdiag_Inr_iff split: option.split vstop.split)

text \<open>The parser's code equation runs \<^const>\<open>vrun_k\<close>, which is only known sound
  for \<^const>\<open>vrun_un\<close>, with \<open>f\<close> numbering the tokens. So an accepted word goes
  through that equation itself, and a rejected one through \<^const>\<open>vdiag\<close> for its
  error, a second pass.\<close>

definition vkdiag :: \<open>('n, 't) vtab \<Rightarrow> ('n, 't) vktab \<Rightarrow> ('n, 't) stab \<Rightarrow> ('n, 't) sitem list \<Rightarrow>
    ('n, 't) sitem list \<Rightarrow> nat \<Rightarrow> ('t \<Rightarrow> nat) \<Rightarrow> 't list \<Rightarrow> (('m, 'ch, 'n, 't) ast \<Rightarrow> 'x option) \<Rightarrow>
    ('m, 'ch, 't) tword \<Rightarrow> ('n, 't, 'ch, 'm) perr + 'x\<close> where
  \<open>vkdiag V K T kin kcl i\<^sub>0 f ts dec w =
     (case Option.bind (case vrun_k K [v_av0 V] (vtnum f w) w [] of
         Some r \<Rightarrow> r | None \<Rightarrow> sdrun T (([kin], tcols w), [kcl], [i\<^sub>0], w, [])) dec of
        Some x \<Rightarrow> Inr x
      | None \<Rightarrow> Inl (projl (vdiag V T kin kcl i\<^sub>0 ts (\<lambda>_. None :: unit option) w)))\<close>

lemma vkdiag_Inr_iff:
  \<open>vkdiag V K T kin kcl i\<^sub>0 f ts dec w = Inr x \<longleftrightarrow>
     Option.bind (case vrun_k K [v_av0 V] (vtnum f w) w [] of
         Some r \<Rightarrow> r | None \<Rightarrow> sdrun T (([kin], tcols w), [kcl], [i\<^sub>0], w, [])) dec = Some x\<close>
  unfolding vkdiag_def by (simp split: option.split)

section \<open>Messages\<close>

text \<open>An error as a message a person can act on, after Pottier (2016, Fig. 7):
  a position, a primary text and notes, as a record (\<open>pmsg\<close>) that a client may
  render its own way, and a default rendering into one string. The text of the
  tokens is in the type \<open>'ch\<close> of the token record, so the caller supplies a
  function \<open>'ch \<Rightarrow> string\<close>; the parser command does so for \<^typ>\<open>char\<close>. Line
  and column are printed as the lexer put them into the spans.\<close>

subsection \<open>What the parser was reading\<close>

text \<open>The terminals a nonterminal may start with: the terminals among the left
  corners reachable from it, where a left corner of a production is any symbol of
  its right-hand side with only nullable symbols before it. The search visits
  each symbol once; its fuel, the number of symbols of the grammar, only makes
  it a total function.\<close>

definition lcorners :: \<open>'n list \<Rightarrow> ('n, 't) rhs \<Rightarrow> ('n, 't) sym list\<close> where
  \<open>lcorners nul rhs = (let xs = map fst rhs in take (Suc (length (takeWhile (nsym nul) xs))) xs)\<close>

fun lreach :: \<open>('n, 't) is_cfg \<Rightarrow> 'n list \<Rightarrow> nat \<Rightarrow> ('n, 't) sym list \<Rightarrow> ('n, 't) sym list \<Rightarrow>
    ('n, 't) sym list\<close> where
  \<open>lreach G nul 0 todo seen = seen\<close>
| \<open>lreach G nul (Suc f) [] seen = seen\<close>
| \<open>lreach G nul (Suc f) (x # todo) seen =
     (if x \<in> set seen then lreach G nul (Suc f) todo seen
      else lreach G nul f
        ((case x of Nt A \<Rightarrow> concat (map (\<lambda>(B, rhs). if B = A then lcorners nul rhs else []) (iprods G))
                  | Tm _ \<Rightarrow> []) @ todo) (x # seen))\<close>

definition nt_first :: \<open>('n, 't) is_cfg \<Rightarrow> 'n list \<Rightarrow> 'n \<Rightarrow> 't list\<close> where
  \<open>nt_first G nul X =
     List.map_filter (\<lambda>x. case x of Tm a \<Rightarrow> Some a | Nt _ \<Rightarrow> None)
       (lreach G nul (Suc (length (concat (map (\<lambda>(A, rhs). Nt A # map fst rhs) (iprods G)))))
          [Nt X] [])\<close>

text \<open>The nonterminals right after the dot in the kernel items of a state: what
  the parser was about to read there.\<close>

definition kernel_nts :: \<open>('n, 't) citem list list \<Rightarrow> nat \<Rightarrow> 'n list\<close> where
  \<open>kernel_nts sts k =
     (if k < length sts
      then remdups (List.map_filter (\<lambda>((A, rhs), m).
             if m < length rhs then (case fst (rhs ! m) of Nt X \<Rightarrow> Some X | Tm _ \<Rightarrow> None) else None)
             (sts ! k))
      else [])\<close>

text \<open>A heuristic, after Pottier (2016, Sect. 4: ``an expression is expected''
  says more than the tokens that may start one): the expected terminals are
  summarised by a nonterminal \<open>X\<close> when the kernel of the state after the last
  shift has an item with the dot before \<open>X\<close> and every terminal that may start
  \<open>X\<close> is expected. The result: the nonterminals, and the expected terminals none
  of them covers.\<close>

definition nt_summary :: \<open>('n, 't) is_cfg \<Rightarrow> 'n list \<Rightarrow> 't list \<Rightarrow> 'n list \<times> 't list\<close> where
  \<open>nt_summary G xs ex =
     (let nul = nullables G;
          fs = map (\<lambda>X. (X, nt_first G nul X)) xs;
          cov = filter (\<lambda>(X, F). F \<noteq> [] \<and> set F \<subseteq> set ex) fs
      in (map fst cov, filter (\<lambda>t. \<not> list_ex (\<lambda>(X, F). t \<in> set F) cov) ex))\<close>

subsection \<open>Text\<close>

fun nat_str :: \<open>nat \<Rightarrow> string\<close> where
  \<open>nat_str n = (if n < 10 then [char_of (48 + n)] else nat_str (n div 10) @ [char_of (48 + n mod 10)])\<close>

definition join_or :: \<open>string list \<Rightarrow> string\<close> where
  \<open>join_or xs = (case rev xs of
       [] \<Rightarrow> []
     | [x] \<Rightarrow> x
     | x # ys \<Rightarrow> concat (map (\<lambda>y. y @ '', '') (butlast (rev ys))) @ last (rev ys) @ '' or '' @ x)\<close>

definition squote :: \<open>string \<Rightarrow> string\<close> where
  \<open>squote s = CHR 0x27 # s @ [CHR 0x27]\<close>

definition article :: \<open>string \<Rightarrow> string\<close> where
  \<open>article s = (case s of c # _ \<Rightarrow> if c \<in> set ''aeiouAEIOU'' then ''an '' @ s else ''a '' @ s
                        | [] \<Rightarrow> s)\<close>

text \<open>The text of a run of tokens, with their spans: tokens on one line are
  separated as in the source, tokens on different lines by one space; a long
  text keeps its start and its end. Tokens without text (over \<^typ>\<open>unit\<close>)
  give none.\<close>

definition span_text :: \<open>('ch \<Rightarrow> string) \<Rightarrow> 'ch span list \<Rightarrow> string\<close> where
  \<open>span_text chs ss = (case ss of
       [] \<Rightarrow> []
     | s # rest \<Rightarrow>
         let txt = (\<lambda>s. concat (map chs (s_txt s)));
             (r, _) = fold (\<lambda>s (acc, p).
               (acc @ (if s_line s = s_line p then replicate (s_col s - (s_col p + s_len p)) (CHR '' '')
                       else '' '') @ txt s, s)) rest (txt s, s)
         in if list_all (\<lambda>s. txt s = []) ss then []
            else if length r \<le> 60 then r else take 28 r @ '' ... '' @ drop (length r - 28) r)\<close>

definition col_text :: \<open>colset \<Rightarrow> string\<close> where
  \<open>col_text cs =
     (case cs of [(a, Some b)] \<Rightarrow> if a = b then ''column '' else ''columns ''
        | [(a, None)] \<Rightarrow> ''column '' | _ \<Rightarrow> ''columns '') @
     join_or (map (\<lambda>(a, b). case b of
         None \<Rightarrow> nat_str a @ '' or further''
       | Some b \<Rightarrow> if a = b then nat_str a else nat_str a @ ''..'' @ nat_str b) cs)\<close>

subsection \<open>The message\<close>

text \<open>A message: where (line, column, offset and length of the offending
  token; at the end of the input the position right after the last token, with
  length \<open>0\<close>), the primary text, and notes.\<close>

record pmsg =
  pm_line :: nat
  pm_col :: nat
  pm_off :: nat
  pm_len :: nat
  pm_text :: string
  pm_notes :: \<open>string list\<close>

text \<open>The key of a hand-written message (Jeffery 2003, Pottier 2016): the state where
  the error is detected, that state with the offending terminal (\<open>None\<close> at the end of
  the input), or the state after the last shift, before the reductions the
  offending token triggered. The first is the default, as in Pottier: words that
  differ in their spurious reductions reach different keys, each its own sentence. Keys are
  state numbers of one build, but they are computed from the sentences at each
  elaboration, so a grammar edit that renumbers states is harmless; only the
  meaning of a message can go stale (Pottier 2016, Sect. 6).\<close>

datatype 't pkey = PState nat | PToken nat \<open>'t option\<close> | PShift nat

text \<open>What a message needs beyond the error: the grammar, the states of the
  parser (for their kernels), the spelling of each terminal, the display name of
  a nonterminal, up to how many expected terminals are listed before they
  are summarised by nonterminals, and the hand-written messages.\<close>

record ('n, 't) pinfo =
  pi_G :: \<open>('n, 't) is_cfg\<close>
  pi_states :: \<open>('n, 't) citem list list\<close>
  pi_spell :: \<open>('t \<times> string) list\<close>
  pi_nt :: \<open>'n \<Rightarrow> string\<close>
  pi_k :: nat
  pi_msgs :: \<open>('t pkey \<times> string) list\<close>

definition tspell :: \<open>('n, 't) pinfo \<Rightarrow> 't \<Rightarrow> string\<close> where
  \<open>tspell I t = (case map_of (pi_spell I) t of Some s \<Rightarrow> s | None \<Rightarrow> ''?'')\<close>

text \<open>A token: its text, or the spelling of its terminal when it has none.\<close>

definition tok_text :: \<open>('n, 't) pinfo \<Rightarrow> ('ch \<Rightarrow> string) \<Rightarrow> ('t, 'ch, 'm) token_scheme \<Rightarrow> string\<close> where
  \<open>tok_text I chs x = (case concat (map chs (s_txt (span x))) of [] \<Rightarrow> tspell I (tok x) | s \<Rightarrow> s)\<close>

definition sym_text :: \<open>('n, 't) pinfo \<Rightarrow> ('n, 't) sym \<Rightarrow> string\<close> where
  \<open>sym_text I X = (case X of Nt A \<Rightarrow> pi_nt I A | Tm t \<Rightarrow> squote (tspell I t))\<close>

text \<open>The span of the last token read: the last token of the topmost entry of
  the stack that has one.\<close>

definition last_span :: \<open>(('n, 't) sym \<times> 'ch span list) list \<Rightarrow> 'ch span option\<close> where
  \<open>last_span stk = (case filter (\<lambda>(X, ss). ss \<noteq> []) stk of [] \<Rightarrow> None | (X, ss) # _ \<Rightarrow> Some (last ss))\<close>

text \<open>The expected things: on a layout grammar, when there is an offending token,
  the terminals accepted at its column; then the nonterminal summary when more
  than \<^const>\<open>pi_k\<close> terminals are expected; and the end of the input.\<close>

definition expected_text :: \<open>('n, 't) pinfo \<Rightarrow> ('n, 't, 'ch, 'm) perr \<Rightarrow> string list\<close> where
  \<open>expected_text I e =
     (let ex = (case (pe_tok e, pe_columns e) of
                  (Some x, _ # _) \<Rightarrow> map fst (filter (\<lambda>(t, cs). col_in (s_col (span x)) cs) (pe_columns e))
                | _ \<Rightarrow> pe_expected e);
          (ns, ts) = (if length ex \<le> pi_k I then ([], ex)
                      else nt_summary (pi_G I) (kernel_nts (pi_states I) (pe_shift_state e)) ex)
      in map (\<lambda>X. article (pi_nt I X)) ns @ map (\<lambda>t. squote (tspell I t)) ts @
         (if pe_expect_end e then [''end of input''] else []))\<close>

text \<open>What was recognised up to here: the topmost entry of the stack if it is a
  nonterminal, otherwise the text of the topmost three entries.\<close>

definition upto_text :: \<open>('n, 't) pinfo \<Rightarrow> ('ch \<Rightarrow> string) \<Rightarrow> ('n, 't, 'ch, 'm) perr \<Rightarrow> string list\<close> where
  \<open>upto_text I chs e = (case pe_stack e of
       [] \<Rightarrow> []
     | (Nt A, ss) # _ \<Rightarrow>
         if ss = [] then [] else
           [''up to here: '' @ article (pi_nt I A) @ '' was recognised'' @
            (case span_text chs ss of [] \<Rightarrow> [] | t \<Rightarrow> '': '' @ squote t)]
     | _ \<Rightarrow> (case span_text chs (concat (rev (map snd (take 3 (pe_stack e))))) of
         [] \<Rightarrow> []
       | s \<Rightarrow> [''up to here: '' @ squote s]))\<close>

text \<open>The template of the error, the most specific key first.\<close>

definition phand :: \<open>('n, 't) pinfo \<Rightarrow> ('n, 't, 'ch, 'm) perr \<Rightarrow> string option\<close> where
  \<open>phand I e =
     (let find = map_of (pi_msgs I)
      in case find (PToken (pe_state e) (map_option tok (pe_tok e))) of
           Some s \<Rightarrow> Some s
         | None \<Rightarrow> (case find (PState (pe_state e)) of
             Some s \<Rightarrow> Some s
           | None \<Rightarrow> find (PShift (pe_shift_state e))))\<close>

text \<open>The text of a stack entry, topmost first: of its tokens, or its symbol when
  it has none. Past the bottom of the stack it is empty.\<close>

definition stack_text :: \<open>('n, 't) pinfo \<Rightarrow> ('ch \<Rightarrow> string) \<Rightarrow> ('n, 't, 'ch, 'm) perr \<Rightarrow> nat \<Rightarrow> string\<close> where
  \<open>stack_text I chs e i = (case drop i (pe_stack e) of
       [] \<Rightarrow> []
     | (X, ss) # _ \<Rightarrow> (case span_text chs ss of [] \<Rightarrow> sym_text I X | t \<Rightarrow> t))\<close>

text \<open>A template with its holes \<open>$0\<close> to \<open>$9\<close> filled: a hole is one digit, and
  a \<open>$\<close> without a digit stands for itself.\<close>

fun fill_holes :: \<open>(nat \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> string\<close> where
  \<open>fill_holes f (c # d # s) =
     (if c = CHR ''$'' \<and> 48 \<le> (of_char d :: nat) \<and> (of_char d :: nat) \<le> 57
      then f (of_char d - 48) @ fill_holes f s
      else c # fill_holes f (d # s))\<close>
| \<open>fill_holes f s = s\<close>

definition perr_message :: \<open>('n, 't) pinfo \<Rightarrow> ('ch \<Rightarrow> string) \<Rightarrow> ('n, 't, 'ch, 'm) perr \<Rightarrow> pmsg\<close> where
  \<open>perr_message I chs e =
     (let after = (case last_span (pe_stack e) of
                     None \<Rightarrow> []
                   | Some s \<Rightarrow> (case concat (map chs (s_txt s)) of [] \<Rightarrow> [] | t \<Rightarrow> '' (after '' @ squote t @ '')''));
          (l, c, off, n, what) = (case pe_tok e of
             Some x \<Rightarrow> (s_line (span x), s_col (span x), s_off (span x), s_len (span x), squote (tok_text I chs x))
           | None \<Rightarrow> (case last_span (pe_stack e) of
               None \<Rightarrow> (0, 0, 0, 0, ''end of input'')
             | Some s \<Rightarrow> (s_line s, s_col s + s_len s, s_off s + s_len s, 0, ''end of input'')));
          anchor = (\<lambda>v. case pe_anchor e of
             None \<Rightarrow> []
           | Some a \<Rightarrow> '' ('' @ v @ '' '' @ squote (tok_text I chs a) @ '' at '' @
                        nat_str (s_line (span a)) @ '':'' @ nat_str (s_col (span a)) @ '')'');
          text = (case phand I e of Some t \<Rightarrow> fill_holes (stack_text I chs e) t | None \<Rightarrow> (case pe_kind e of
             Misaligned cs \<Rightarrow> what @ '' at column '' @ nat_str c @ '' must be at '' @ col_text cs @
               anchor ''aligned with''
           | Offside cs \<Rightarrow> what @ '' at column '' @ nat_str c @ '' must be at '' @ col_text cs @
               anchor ''indented from''
           | ReduceCycle \<Rightarrow> ''the parser loops on a cycle of reductions at '' @ what @ after
           | NoAction \<Rightarrow> ''syntax error at '' @ what @ after));
          ex = expected_text I e
      in \<lparr>pm_line = l, pm_col = c, pm_off = off, pm_len = n, pm_text = text,
          pm_notes = (if ex = [] then [] else [''expected: '' @ join_or ex]) @ upto_text I chs e\<rparr>)\<close>

text \<open>What the command reads from a sentence of an \<^text>\<open>errors\<close> block: the
  state, the offending terminal, the state after the last shift, the index of the
  offending token and the depth of the stack; \<open>None\<close> if the word is accepted.\<close>

fun diag_probe :: \<open>('n, 't, 'ch, 'm) perr + 'x \<Rightarrow> (nat \<times> 't option \<times> nat \<times> nat \<times> nat) option\<close> where
  \<open>diag_probe (Inl e) = Some (pe_state e, map_option tok (pe_tok e), pe_shift_state e,
     pe_index e, length (pe_stack e))\<close>
| \<open>diag_probe (Inr _) = None\<close>

definition pmsg_lines :: \<open>pmsg \<Rightarrow> string list\<close> where
  \<open>pmsg_lines m = (nat_str (pm_line m) @ '':'' @ nat_str (pm_col m) @ '': '' @ pm_text m) #
     map (\<lambda>s. ''  '' @ s) (pm_notes m)\<close>

definition perr_render :: \<open>('n, 't) pinfo \<Rightarrow> ('ch \<Rightarrow> string) \<Rightarrow> ('n, 't, 'ch, 'm) perr \<Rightarrow> string\<close> where
  \<open>perr_render I chs e = (case pmsg_lines (perr_message I chs e) of
     [] \<Rightarrow> [] | l # ls \<Rightarrow> l @ concat (map (\<lambda>s. CHR 0x0A # s) ls))\<close>

end
