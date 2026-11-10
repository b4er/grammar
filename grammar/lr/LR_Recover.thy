theory LR_Recover
  imports LR_Diag
begin

section \<open>Recovering from a rejected word\<close>

text \<open>A rejected word is rewritten into one that parses, and the verified parser
  runs on the result. The user adds an ordinary error token to the token type and
  alternatives such as \<open>Expr = \<dots> | ERR\<close>, so the grammar stays an ordinary grammar,
  and \<^text>\<open>parser (diagnostics) p for G recover ERR\<close> defines \<open>p_repair\<close>, the
  rewriter, and \<open>p_recover\<close>. The tree of a rewritten word is a tree of that word:
  \<open>p.sound\<close> is the whole story, and nothing is proved about the rewriter.

  The rewriter follows Menhir's \<open>error\<close> token. At a stop, it pops the stack to a
  configuration that can shift the error token, skips the input until the parser
  can continue after that token, and replaces the tokens popped and skipped by one
  error token. Popped entries give the input they cover by the number of their
  tokens. Then it starts over on the new word, for the next error.

  Where no error token fits, or the grammar has none, it searches for a repair
  sequence as in CPCT+ (Diekmann and Tratt 2020): tokens inserted, deleted and
  kept. See \<open>rcpct\<close>.\<close>

subsection \<open>A plan\<close>

text \<open>What the search needs from a driver, on a configuration \<open>'c\<close> without tokens:
  the configuration past the shift of a terminal at a column, whether the end of
  the input is accepted, the stack with its top entry popped, and the columns
  to try. \<open>ro_can\<close> is a test of a terminal before it is tried at the columns: one that
  fails it may be skipped, so it is \<open>False\<close> only where every column fails.\<close>

record ('c, 't) rops =
  ro_adv :: \<open>'c \<Rightarrow> 't \<times> nat \<Rightarrow> 'c option\<close>
  ro_end :: \<open>'c \<Rightarrow> bool\<close>
  ro_pop :: \<open>'c \<Rightarrow> 'c option\<close>
  ro_cols :: \<open>'c \<Rightarrow> nat list\<close>
  ro_can :: \<open>'c \<Rightarrow> 't \<Rightarrow> bool\<close>

text \<open>As \<^const>\<open>dtrial\<close>, but it returns the configuration past the shift.\<close>

partial_function (option) dadv ::
  \<open>('c \<Rightarrow> (('n, 't) dact \<times> 'c) option) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'k list) \<Rightarrow>
    'k list option \<times> nat \<times> nat \<Rightarrow> 'c \<Rightarrow> 'c option\<close>
  where
  \<open>dadv ctl fin key d c =
     (if fin c \<or> fst d = Some (key c) then None
      else (case ctl c of
        None \<Rightarrow> None
      | Some (act, c') \<Rightarrow>
          if act = DShift then Some c' else dadv ctl fin key (bupd d (key c)) c'))\<close>

lemmas dadv_simps [code] = dadv.simps

text \<open>The first column at which \<open>f\<close> succeeds.\<close>

fun rfirst :: \<open>(nat \<Rightarrow> 'c option) \<Rightarrow> nat list \<Rightarrow> (nat \<times> 'c) option\<close> where
  \<open>rfirst f [] = None\<close>
| \<open>rfirst f (k # ks) = (case f k of Some c \<Rightarrow> Some (k, c) | None \<Rightarrow> rfirst f ks)\<close>

text \<open>How many tokens to skip until the parser can continue: skipping none means
  that the error token is inserted.\<close>

fun rskip :: \<open>('c, 't) rops \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> ('t \<times> nat) list \<Rightarrow> nat option\<close> where
  \<open>rskip ops c s [] = (if ro_end ops c then Some s else None)\<close>
| \<open>rskip ops c s (x # xs) = (if ro_adv ops c x \<noteq> None then Some s else rskip ops c (Suc s) xs)\<close>

text \<open>The column of the error token: the column of the input it replaces if it
  fits there. Otherwise the nearest one that fits, so that a misplaced token can be
  replaced: this is the only field of the error token's span that may differ from
  the input, as the parser reads it from there. Between two tried columns acceptance
  is constant, see \<^const>\<open>lreps\<close>.\<close>

definition rhere :: \<open>('c, 't) rops \<Rightarrow> 't \<Rightarrow> nat \<Rightarrow> ('t \<times> nat) list \<Rightarrow> 'c \<Rightarrow> (nat \<times> nat) option\<close> where
  \<open>rhere ops e k xs c =
     (case rfirst (\<lambda>r. ro_adv ops c (e, r))
             (k # sort_key (\<lambda>r. if r \<le> k then k - r else r - k) (ro_cols ops c)) of
        None \<Rightarrow> None
      | Some (k', c') \<Rightarrow> map_option (\<lambda>s. (k', s)) (rskip ops c' 0 xs))\<close>

definition alen :: \<open>('m, 'ch, 'n, 't) ast \<Rightarrow> nat\<close> where
  \<open>alen t = length (aspans t [])\<close>

text \<open>The column of the input at index \<open>a\<close>, at the end of the input right after
  the last token.\<close>

definition rcol :: \<open>('m, 'ch, 't) tword \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>rcol w a = (if a < length w then s_col (span (w ! a))
     else let s = span (last w) in s_col s + s_len s)\<close>

text \<open>A plan: replace the tokens from index \<open>a\<close> up to \<open>b\<close> by an error token at
  column \<open>k\<close>. The stack goes down from the configuration \<open>c\<close> at index \<open>i\<close>; the
  index \<open>a\<close> follows it, and the first configuration that works is taken, so the
  innermost construct takes the error.\<close>

type_synonym rplan = \<open>nat \<times> nat \<times> nat\<close>

fun rsearch :: \<open>('c, 't) rops \<Rightarrow> 't \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow>
    ('m, 'ch, 'n, 't) ast list \<Rightarrow> rplan option\<close> where
  \<open>rsearch ops e w i a c [] =
     map_option (\<lambda>(k, s). (a, i + s, k)) (rhere ops e (rcol w a) (tcols (drop i w)) c)\<close>
| \<open>rsearch ops e w i a c (t # ts) =
     (case rhere ops e (rcol w a) (tcols (drop i w)) c of
        Some (k, s) \<Rightarrow> Some (a, i + s, k)
      | None \<Rightarrow> (case ro_pop ops c of
          None \<Rightarrow> None
        | Some c' \<Rightarrow> rsearch ops e w i (a - alen t) c' ts))\<close>

subsection \<open>The new word\<close>

text \<open>The span of the error token at column \<open>k\<close>: it runs from the first replaced
  token to the last, with their text. If nothing is replaced it is empty, in
  front of the token at \<open>a\<close> or after the last token.\<close>

definition rspan :: \<open>('m, 'ch, 't) tword \<Rightarrow> nat \<Rightarrow> ('t, 'ch, 'm) token_scheme list \<Rightarrow> nat \<Rightarrow> 'ch span\<close> where
  \<open>rspan w a ss k = (case ss of
       [] \<Rightarrow> if a < length w
             then (span (w ! a))\<lparr>s_col := k, s_len := 0, s_txt := []\<rparr>
             else let s = span (last w) in
               s\<lparr>s_col := k, s_off := s_off s + s_len s, s_len := 0, s_txt := []\<rparr>
     | f # _ \<Rightarrow> let l = span (last ss) in
         (span f)\<lparr>s_col := k, s_len := s_off l + s_len l - s_off (span f),
                  s_txt := concat (map (s_txt \<circ> span) ss)\<rparr>)\<close>

text \<open>The error token is a replaced token or a neighbour with its terminal and span
  changed, so a token record extended by the user keeps its fields.\<close>

definition rsplice :: \<open>'t \<Rightarrow> rplan \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> ('m, 'ch, 't) tword\<close> where
  \<open>rsplice e p w = (case p of (a, b, k) \<Rightarrow>
     let ss = take (b - a) (drop a w);
         x = (if ss \<noteq> [] then last ss else if a < length w then w ! a else last w)
     in take a w @ [x\<lparr>tok := e, span := rspan w a ss k\<rparr>] @ drop b w)\<close>

subsection \<open>Repair sequences\<close>

text \<open>The search of Diekmann and Tratt (2020, Fig. 6, Sect. 5) over configurations
  \<open>'c\<close>, for the configuration after the last shift. A node holds a configuration,
  the input left, the number of tokens kept in a row and the repair so far, last
  step first. Keeping a token costs 0, inserting or deleting one costs 1, and a
  delete is not followed by an insert (Fig. 6, line 12). A node succeeds at the
  end of the input if that is accepted, or after \<open>rnshifts\<close> tokens kept.

  Their reduction-only step (CR Shift 3) is not needed: \<^const>\<open>ro_adv\<close> runs from
  the configuration after the last shift with the terminal as lookahead, so it does
  the reductions that terminal licenses. Reductions it does not license would give
  a word the parser rejects, and this search rewrites words.

  Compatible nodes are merged (their Sect. 5.2), see \<open>rkey\<close>. HOL has no clock,
  so a budget of nodes replaces their timeout (Sect. 5.4): \<open>rnodes\<close> nodes for
  the whole word, so that several stops do not add up. It counts the nodes searched,
  which take most of the time of a repair, and merged nodes are free. An inserted
  terminal takes the column of the token it stands in front of if it fits there,
  otherwise the nearest that fits, as the error token does in \<^const>\<open>rhere\<close>.\<close>

definition rnshifts :: nat where \<open>rnshifts = 3\<close>

definition rntry :: nat where \<open>rntry = 250\<close>

definition rnodes :: nat where \<open>rnodes = 240\<close>

type_synonym ('c, 't) rnode = \<open>'c \<times> ('t \<times> nat) list \<times> nat \<times> 't rop list\<close>

definition rsuccess :: \<open>('c, 't) rops \<Rightarrow> ('c, 't) rnode \<Rightarrow> bool\<close> where
  \<open>rsuccess ops nd = (case nd of (c, xs, n, _) \<Rightarrow> rnshifts \<le> n \<or> (xs = [] \<and> ro_end ops c))\<close>

text \<open>The neighbours of a node, at cost 0 and at cost 1. \<open>ke\<close> is the column at the
  end of the input. The terminals \<open>ts\<close> are tried in their order, which is the
  order of the ties in the ranking.\<close>

definition rnbrs :: \<open>('c, 't) rops \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> ('c, 't) rnode \<Rightarrow>
    ('c, 't) rnode list \<times> ('c, 't) rnode list\<close> where
  \<open>rnbrs ops ts ke nd = (case nd of (c, xs, n, os) \<Rightarrow>
     let k = (case xs of [] \<Rightarrow> ke | x # _ \<Rightarrow> snd x);
         cs = k # sort_key (\<lambda>r. if r \<le> k then k - r else r - k) (ro_cols ops c);
         ins = (case os of RDel _ # _ \<Rightarrow> []
           | _ \<Rightarrow> List.map_filter (\<lambda>t. if \<not> ro_can ops c t then None
                    else map_option (\<lambda>(r, c'). (c', xs, 0, RIns t r # os))
                      (rfirst (\<lambda>r. ro_adv ops c (t, r)) cs)) ts)
     in (case xs of
           [] \<Rightarrow> ([], ins)
         | x # xs' \<Rightarrow>
             (case ro_adv ops c x of None \<Rightarrow> [] | Some c' \<Rightarrow> [(c', xs', Suc n, RKeep # os)],
              ins @ [(c, xs', 0, RDel (fst x) # os)])))\<close>

text \<open>Fig. 6 gives a node of a key already seen the same future at no less cost, so
  it is dropped, and the first in the search stays: the search picks one repair, so
  it needs no parent pointer trees. A key is that of Sect. 5.2: the configuration, the
  input left, the tokens kept in a row, and whether the repair ends in a delete. It
  adds the inserted terminals of \<open>av\<close>, as they count in the ranking.\<close>

fun rinserted :: \<open>'t rop \<Rightarrow> 't list\<close> where
  \<open>rinserted (RIns t k) = [t]\<close>
| \<open>rinserted _ = []\<close>

definition ravoided :: \<open>'t list \<Rightarrow> 't rop list \<Rightarrow> nat\<close> where
  \<open>ravoided av os = length (filter (\<lambda>t. t \<in> set av) (concat (map rinserted os)))\<close>

fun rdeleted :: \<open>'t rop list \<Rightarrow> bool\<close> where
  \<open>rdeleted (RDel _ # _) = True\<close>
| \<open>rdeleted _ = False\<close>

type_synonym 'c rkey = \<open>'c \<times> nat \<times> nat \<times> bool \<times> nat\<close>

definition rkey :: \<open>'t list \<Rightarrow> ('c, 't) rnode \<Rightarrow> 'c rkey\<close> where
  \<open>rkey av nd = (case nd of (c, xs, n, os) \<Rightarrow> (c, length xs, n, rdeleted os, ravoided av os))\<close>

text \<open>All nodes of one cost: the budget left, the nodes of the next cost, the
  successes in the order of the search, and the keys seen. Their complete set is
  the point of Sect. 5.1, so the level is finished after the first one. If the
  budget runs out the successes so far stand.\<close>

fun rlevel :: \<open>('c, 't) rops \<Rightarrow> 't list \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('c, 't) rnode list \<Rightarrow>
    ('c, 't) rnode list \<Rightarrow> ('c, 't) rnode list \<Rightarrow> 'c rkey list \<Rightarrow>
    nat \<times> ('c, 't) rnode list \<times> ('c, 't) rnode list \<times> 'c rkey list\<close> where
  \<open>rlevel ops ts av ke 0 cur nx ok vs = (0, [], rev ok, vs)\<close>
| \<open>rlevel ops ts av ke (Suc b) [] nx ok vs = (Suc b, rev nx, rev ok, vs)\<close>
| \<open>rlevel ops ts av ke (Suc b) (nd # cur) nx ok vs =
     (let k = rkey av nd in
      if k \<in> set vs then rlevel ops ts av ke (Suc b) cur nx ok vs
      else if rsuccess ops nd then rlevel ops ts av ke b cur nx (nd # ok) (k # vs)
      else (case rnbrs ops ts ke nd of
        (zs, os) \<Rightarrow> rlevel ops ts av ke b (zs @ cur) (rev os @ nx) ok (k # vs)))\<close>

text \<open>The patterns on \<open>b\<close> and on \<open>cur\<close> together do not survive the preprocessing of
  \<open>Code_Target_Numeral\<close>, where \<open>0\<close> is no constructor.\<close>

lemma rlevel_code [code]:
  \<open>rlevel ops ts av ke b cur nx ok vs = (if b = 0 then (0, [], rev ok, vs) else case cur of
     [] \<Rightarrow> (b, rev nx, rev ok, vs)
   | nd # cur' \<Rightarrow>
       let k = rkey av nd in
       if k \<in> set vs then rlevel ops ts av ke b cur' nx ok vs
       else if rsuccess ops nd then rlevel ops ts av ke (b - 1) cur' nx (nd # ok) (k # vs)
       else (case rnbrs ops ts ke nd of
         (zs, os) \<Rightarrow> rlevel ops ts av ke (b - 1) (zs @ cur') (rev os @ nx) ok (k # vs)))\<close>
  by (cases b; cases cur) (simp_all add: Let_def)

fun rcost :: \<open>nat \<Rightarrow> ('c, 't) rops \<Rightarrow> 't list \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('c, 't) rnode list \<Rightarrow>
    'c rkey list \<Rightarrow> nat \<times> ('c, 't) rnode list\<close> where
  \<open>rcost 0 ops ts av ke b cur vs = (b, [])\<close>
| \<open>rcost (Suc f) ops ts av ke b cur vs = (case rlevel ops ts av ke b cur [] [] vs of
     (b', nx, ok, vs') \<Rightarrow> if ok \<noteq> [] \<or> nx = [] then (b', ok) else rcost f ops ts av ke b' nx vs')\<close>

text \<open>The ranking of Sect. 5.3: how far parsing continues, up to \<^const>\<open>rntry\<close>
  tokens, then fewer inserted terminals of \<open>av\<close> (\<open>%avoid_insert\<close>, Sect. 7.3), then
  the first in the search, where they choose at random.\<close>

fun rreach :: \<open>('c, 't) rops \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> ('t \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>rreach ops 0 c xs s = s\<close>
| \<open>rreach ops (Suc f) c xs s = (case xs of
     [] \<Rightarrow> if ro_end ops c then Suc s else s
   | x # xs' \<Rightarrow> (case ro_adv ops c x of None \<Rightarrow> s | Some c' \<Rightarrow> rreach ops f c' xs' (Suc s)))\<close>

fun rkept :: \<open>'t rop \<Rightarrow> bool\<close> where
  \<open>rkept RKeep = True\<close>
| \<open>rkept _ = False\<close>

definition rrank :: \<open>('c, 't) rops \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> ('c, 't) rnode \<Rightarrow> nat \<times> nat\<close> where
  \<open>rrank ops av n nd = (case nd of (c, xs, _, os) \<Rightarrow>
     (rreach ops rntry c xs (n - length xs),
      ravoided av os))\<close>

definition rbest :: \<open>('c, 't) rops \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> ('c, 't) rnode \<Rightarrow> ('c, 't) rnode list \<Rightarrow>
    ('c, 't) rnode\<close> where
  \<open>rbest ops av n nd nds = fst (fold (\<lambda>y (b, br).
     let yr = rrank ops av n y
     in if fst br < fst yr \<or> (fst br = fst yr \<and> snd yr < snd br) then (y, yr) else (b, br))
     nds (nd, rrank ops av n nd))\<close>

text \<open>The best repair of the input \<open>xs\<close> from \<open>c\<close> within \<open>b\<close> nodes, without its
  trailing kept tokens, and the nodes left.\<close>

definition rcpct :: \<open>('c, 't) rops \<Rightarrow> 't list \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> ('t \<times> nat) list \<Rightarrow>
    nat \<times> 't rop list option\<close> where
  \<open>rcpct ops ts av b ke c xs = (case rcost (Suc b) ops ts av ke b [(c, xs, 0, [])] [] of
     (b', oks) \<Rightarrow> (b', case oks of
       [] \<Rightarrow> None
     | nd # nds \<Rightarrow> (case rbest ops av (length xs) nd nds of (_, _, _, os) \<Rightarrow>
         (case rev (dropWhile rkept os) of [] \<Rightarrow> None | r \<Rightarrow> Some r))))\<close>

text \<open>The default token of an inserted terminal, as for the error token: a neighbour
  with its terminal and span changed. A user's \<open>repair_token\<close> ignores the neighbour.\<close>

definition rtoken :: \<open>('t, 'ch, 'm) token_scheme \<Rightarrow> 't \<Rightarrow> 'ch span \<Rightarrow> ('t, 'ch, 'm) token_scheme\<close> where
  \<open>rtoken x t s = x\<lparr>tok := t, span := s\<rparr>\<close>

definition rtoken_user :: \<open>('t \<Rightarrow> 'ch span \<Rightarrow> ('t, 'ch, 'm) token_scheme) \<Rightarrow>
    ('t, 'ch, 'm) token_scheme \<Rightarrow> 't \<Rightarrow> 'ch span \<Rightarrow> ('t, 'ch, 'm) token_scheme\<close> where
  \<open>rtoken_user f x = f\<close>

text \<open>The word from index \<open>a\<close> on, under a repair.\<close>

fun rapply :: \<open>(('t, 'ch, 'm) token_scheme \<Rightarrow> 't \<Rightarrow> 'ch span \<Rightarrow> ('t, 'ch, 'm) token_scheme) \<Rightarrow>
    ('m, 'ch, 't) tword \<Rightarrow> nat \<Rightarrow> 't rop list \<Rightarrow> ('m, 'ch, 't) tword\<close> where
  \<open>rapply mk w a [] = drop a w\<close>
| \<open>rapply mk w a (RKeep # os) = (w ! a) # rapply mk w (Suc a) os\<close>
| \<open>rapply mk w a (RDel _ # os) = rapply mk w (Suc a) os\<close>
| \<open>rapply mk w a (RIns t k # os) =
     mk (if a < length w then w ! a else last w) t (rspan w a [] k) # rapply mk w a os\<close>

subsection \<open>The rewriter\<close>

text \<open>The tokens that must be shifted after an error token before the next error
  is reported, as in Bison and Menhir. A stop before that is recovered from in the
  same way, but it is taken for a consequence of the last recovery. A repair needs
  no such quiet: it succeeded by keeping \<^const>\<open>rnshifts\<close> tokens or at the end.\<close>

definition rquiet :: nat where \<open>rquiet = 3\<close>

text \<open>How to recover: the error token, and for repairs the terminals that may not
  be inserted without need (\<open>av\<close>) and the token of an inserted terminal.\<close>

record ('t, 'ch, 'm) rmode =
  rm_err :: \<open>'t option\<close>
  rm_repair :: \<open>('t list \<times> (('t, 'ch, 'm) token_scheme \<Rightarrow> 't \<Rightarrow> 'ch span \<Rightarrow> ('t, 'ch, 'm) token_scheme)) option\<close>

text \<open>The new word at a stop at index \<open>i\<close>, from the configuration \<open>c\<close> with the AST
  stack \<open>tr\<close>, with the index from which errors count again and the nodes left of
  \<open>b\<close>: a repair over the terminals \<open>ts\<close>, which the error records, otherwise the
  error token if it fits. A repair comes first as it keeps the input, where the error
  token drops what it stands for. The empty word has no neighbour to make a token from.\<close>

definition rfix :: \<open>('c, 't) rops \<Rightarrow> ('t, 'ch, 'm) rmode \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow>
    ('m, 'ch, 'n, 't) ast list \<Rightarrow> ('n, 't, 'ch, 'm) perr \<Rightarrow>
    ('n, 't, 'ch, 'm) perr \<times> (('m, 'ch, 't) tword \<times> nat \<times> nat) option\<close> where
  \<open>rfix ops rm ts b w i c tr x =
     (if w = [] then (x, None)
      else (let (b', r) = (case rm_repair rm of
                   None \<Rightarrow> (b, None)
                 | Some (av, mk) \<Rightarrow> (case rcpct ops ts av b (rcol w (length w)) c (tcols (drop i w)) of
                     (b', r) \<Rightarrow> (b', map_option (Pair mk) r)))
            in (case r of
        Some (mk, os) \<Rightarrow> (x\<lparr>pe_repair := os\<rparr>, Some (take i w @ rapply mk w i os, 0, b'))
      | None \<Rightarrow> (case Option.bind (rm_err rm) (\<lambda>e. map_option (Pair e) (rsearch ops e w i i c tr)) of
          None \<Rightarrow> (x, None)
        | Some (e, p) \<Rightarrow> (x, Some (rsplice e p w, fst p + 1 + rquiet, b'))))))\<close>

text \<open>A stop of the word \<open>w\<close> within \<open>b\<close> nodes, \<open>None\<close> if it is accepted. Each round replaces or
  skips the offending token, or inserts tokens that are followed by it, so the
  input left at the stop gets shorter; the round stops if it does not (the
  trials read one lookahead, as the parser, but where the vector driver has a
  conflict they need not agree with it), and there are at most as many rounds as
  tokens plus one. The errors are in the order of the input, the first is always
  reported, and each index is one of the original word.\<close>

fun rloop :: \<open>(nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> (('n, 't, 'ch, 'm) perr \<times> (('m, 'ch, 't) tword \<times> nat \<times> nat) option) option) \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> ('n, 't, 'ch, 'm) perr list \<Rightarrow>
    ('n, 't, 'ch, 'm) perr list \<times> ('m, 'ch, 't) tword\<close> where
  \<open>rloop stop 0 left safe n b w es = (rev es, w)\<close>
| \<open>rloop stop (Suc f) left safe n b w es = (case stop b w of
     None \<Rightarrow> (rev es, w)
   | Some (x, pl) \<Rightarrow>
       let i = pe_index x;
           es' = (if safe \<le> i \<or> es = [] then x\<lparr>pe_index := i + n - length w\<rparr> # es else es);
           left' = length w - i
       in (case pl of
             Some (w', sf, b') \<Rightarrow> if left' < left
               then rloop stop f left' sf n b' w' es'
               else (rev es', w)
           | None \<Rightarrow> (rev es', w)))\<close>

definition repair :: \<open>(nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> (('n, 't, 'ch, 'm) perr \<times> (('m, 'ch, 't) tword \<times> nat \<times> nat) option) option) \<Rightarrow>
    ('m, 'ch, 't) tword \<Rightarrow> ('n, 't, 'ch, 'm) perr list \<times> ('m, 'ch, 't) tword\<close> where
  \<open>repair stop w = rloop stop (Suc (length w)) (Suc (length w)) 0 (length w) rnodes w []\<close>

text \<open>The parser with recovery: a word \<open>p\<close> accepts costs what \<open>p\<close> costs and gives no
  errors. Otherwise \<open>p\<close> runs on the rewritten word, and the errors are not empty.\<close>

definition precover :: \<open>('w \<Rightarrow> 'x option) \<Rightarrow> ('w \<Rightarrow> 'e list \<times> 'w) \<Rightarrow> 'w \<Rightarrow> 'e list \<times> 'x option\<close> where
  \<open>precover p rep w = (case p w of
     Some x \<Rightarrow> ([], Some x)
   | None \<Rightarrow> (case rep w of
       ([], _) \<Rightarrow> ([], None)
     | (e # es, w') \<Rightarrow> (e # es, p w')))\<close>

lemma precover_clean:
  assumes \<open>f \<equiv> precover p rep\<close> and \<open>f w = ([], Some x)\<close>
  shows \<open>p w = Some x\<close>
  using assms by (auto simp: precover_def split: option.splits prod.splits list.splits)

subsection \<open>The adapters\<close>

text \<open>A stop of the engine: the error, and the plan from the configuration after
  the last shift, before the reductions the offending token triggered, as the
  trials of the expected terminals. A cycle has no plan.\<close>

definition rstop :: \<open>('n, 't, 'ch, 'm) perr \<Rightarrow>
    ('c \<times> ('m, 'ch, 'n, 't) ast list \<Rightarrow> ('n, 't, 'ch, 'm) perr \<times> ('w \<times> nat \<times> nat) option) \<Rightarrow>
    ('c, ('m, 'ch, 'n, 't) ast) dstop option \<Rightarrow> (('n, 't, 'ch, 'm) perr \<times> ('w \<times> nat \<times> nat) option) option\<close> where
  \<open>rstop x pl r = (case r of
       None \<Rightarrow> Some (x, None)
     | Some (DDone _) \<Rightarrow> None
     | Some (DStuck NoAction _ sh) \<Rightarrow> Some (pl sh)
     | Some (DStuck _ _ _) \<Rightarrow> Some (x, None))\<close>

text \<open>The layout-free adapter, on the stack of states.\<close>

definition pops :: \<open>('n, 't) ptabs \<Rightarrow> ('t \<Rightarrow> nat) \<Rightarrow> (nat list, 't) rops\<close> where
  \<open>pops P f =
     \<lparr>ro_adv = \<lambda>stk x. map_option fst
        (dadv (pctl P) (pfinal P) fst (None, 1, 1) (ptrial f stk (Some (fst x)))),
      ro_end = \<lambda>stk. dtrial (pctl P) (pfinal P) fst (None, 1, 1) (ptrial f stk None) = Some True,
      ro_pop = \<lambda>stk. (case stk of _ # y # ys \<Rightarrow> Some (y # ys) | _ \<Rightarrow> None),
      ro_cols = \<lambda>_. [],
      ro_can = \<lambda>_ _. True\<rparr>\<close>

definition prstop :: \<open>('n, 't) ptabs \<Rightarrow> nat \<Rightarrow> ('t \<Rightarrow> nat) \<Rightarrow> 't list \<Rightarrow> ('t, 'ch, 'm) rmode \<Rightarrow>
    nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> (('n, 't, 'ch, 'm) perr \<times> (('m, 'ch, 't) tword \<times> nat \<times> nat) option) option\<close> where
  \<open>prstop P i0 f ts rm b w =
     (let r = pdiag_run P i0 f w;
          x = dperr pstate snd fst (pexpect P f ts) (length w) r
      in rstop x (\<lambda>sh. rfix (pops P f) rm ts b w (length w - length (snd (fst sh))) (fst (fst sh)) (snd sh) x) r)\<close>

text \<open>The set-anchored adapter, over the step at the token type of the trials.\<close>

definition lpop :: \<open>('m, 'ch, 'p, 't) lcfg \<Rightarrow> ('m, 'ch, 'p, 't) lcfg option\<close> where
  \<open>lpop c = (case c of (((Xs, w), cstk, istk, v), n) \<Rightarrow>
     (case Xs of _ # _ # _ \<Rightarrow> Some (((tl Xs, w), tl cstk, tl istk, v), n - 1) | _ \<Rightarrow> None))\<close>

definition lops :: \<open>(unit, unit, 'p, 'n, 't) astep \<Rightarrow> (('p, 't) agconfig \<Rightarrow> bool) \<Rightarrow>
    ((unit, unit, 'p, 't) lcfg, 't) rops\<close> where
  \<open>lops stp fin =
     \<lparr>ro_adv = \<lambda>c x. dadv (lctl stp) (lfin fin) lkey (None, 1, 1) (ltrial c (Some x)),
      ro_end = \<lambda>c. ltry stp fin c None,
      ro_pop = lpop,
      ro_cols = lreps,
      ro_can = \<lambda>_ _. True\<rparr>\<close>

definition lrstop :: \<open>('m, 'ch, 'p, 'n, 't) astep \<Rightarrow> (unit, unit, 'p, 'n, 't) astep \<Rightarrow>
    (('p, 't) agconfig \<Rightarrow> bool) \<Rightarrow> 'p aitem list \<Rightarrow> 'p aitem list \<Rightarrow> nat \<Rightarrow> 't list \<Rightarrow> ('t, 'ch, 'm) rmode \<Rightarrow>
    nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> (('n, 't, 'ch, 'm) perr \<times> (('m, 'ch, 't) tword \<times> nat \<times> nat) option) option\<close> where
  \<open>lrstop stp stpu fin xin xclos i\<^sub>0 ts rm b w =
     (let r = ldiag_run stp fin xin xclos i\<^sub>0 w;
          x = ldperr stpu fin ts (length w) r
      in rstop x (\<lambda>sh. rfix (lops stpu fin) rm ts b w (length w - length (linp (fst sh)))
                   (ltrial (fst sh) None) (snd sh) x) r)\<close>

definition drstop :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> ('n, 't) xitem list \<Rightarrow>
    ('n, 't) xitem list \<Rightarrow> nat \<Rightarrow> 't list \<Rightarrow> ('t, 'ch, 'm) rmode \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow>
    (('n, 't, 'ch, 'm) perr \<times> (('m, 'ch, 't) tword \<times> nat \<times> nat) option) option\<close> where
  \<open>drstop G Shn gt sts redtab xin xclos i\<^sub>0 ts rm b w =
     lrstop (dstep_act G gt sts redtab) (dstep_act G gt sts redtab) (gfinal G Shn) xin xclos i\<^sub>0 ts rm b w\<close>

definition srstop :: \<open>('n, 't) stab \<Rightarrow> ('n, 't) sitem list \<Rightarrow> ('n, 't) sitem list \<Rightarrow> nat \<Rightarrow>
    't list \<Rightarrow> ('t, 'ch, 'm) rmode \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow>
    (('n, 't, 'ch, 'm) perr \<times> (('m, 'ch, 't) tword \<times> nat \<times> nat) option) option\<close> where
  \<open>srstop T kin kcl i\<^sub>0 ts rm b w =
     lrstop (sdstep_dact T) (sdstep_dact T) (sgfinal T) kin kcl i\<^sub>0 ts rm b w\<close>

text \<open>The vector adapter. Where the run meets a conflict it restarts on the sparse
  driver, as the parser does.\<close>

partial_function (option) vadv :: \<open>('n, 't) vtab \<Rightarrow> vcfg \<Rightarrow> vcfg option\<close> where
  \<open>vadv V c = (case c of (fs, w) \<Rightarrow> (case fs of [] \<Rightarrow> None | (j, av) # _ \<Rightarrow>
     (case vpick_n V c (vcands_n V j av w) of
        None \<Rightarrow> None
      | Some (a, c') \<Rightarrow> (case a of VShift \<Rightarrow> Some c' | VReduce _ _ _ \<Rightarrow> vadv V c'))))\<close>

lemmas vadv_simps [code] = vadv.simps

text \<open>The search tries every terminal at every column it tells apart, and on a large grammar
  most of these trials fail at all of them. A trial that succeeds has, on the stack of states
  alone, a shift of the terminal or a reduction listed for it as lookahead whose goto
  exists, and so on down to a shift: \<open>vshiftable\<close>, without the columns and the frames, true
  when its fuel runs out. It is the \<^const>\<open>ro_can\<close> of the adapter, checked once per
  terminal and node (\<open>vops_f_can\<close>); \<open>vshiftable_s\<close> is the same on states kept in front of
  the frames, so the frames are not copied.\<close>

fun vhd :: \<open>nat list \<Rightarrow> nat option\<close> where
  \<open>vhd [] = None\<close>
| \<open>vhd (j # _) = Some j\<close>

fun vshiftable :: \<open>('n, 't) vtab \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>vshiftable V a 0 js = True\<close>
| \<open>vshiftable V a (Suc n) js = (case vhd js of None \<Rightarrow> False | Some j \<Rightarrow>
     iget (iget (v_sh V) j (IArray [])) a None \<noteq> None \<or>
     list_ex (\<lambda>(s, b, pr). list_ex (\<lambda>(s', _). s' = s) (iget (iget (v_cl V) j (IArray [])) a []) \<and>
       (let js' = drop (length (snd pr)) js in
        case vhd js' of None \<Rightarrow> False
        | Some j\<^sub>0 \<Rightarrow> (case iget (iget (v_go V) j\<^sub>0 (IArray [])) b None of None \<Rightarrow> False
            | Some e \<Rightarrow> vshiftable V a n (fst e # js'))))
       (iget (v_cp V) j []))\<close>

fun vhd_s :: \<open>nat list \<Rightarrow> vframes \<Rightarrow> nat option\<close> where
  \<open>vhd_s (j # _) fs = Some j\<close>
| \<open>vhd_s [] [] = None\<close>
| \<open>vhd_s [] ((j, _) # _) = Some j\<close>

fun vshiftable_s :: \<open>('n, 't) vtab \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> vframes \<Rightarrow> bool\<close> where
  \<open>vshiftable_s V a 0 js fs = True\<close>
| \<open>vshiftable_s V a (Suc n) js fs = (case vhd_s js fs of None \<Rightarrow> False | Some j \<Rightarrow>
     iget (iget (v_sh V) j (IArray [])) a None \<noteq> None \<or>
     list_ex (\<lambda>(s, b, pr). list_ex (\<lambda>(s', _). s' = s) (iget (iget (v_cl V) j (IArray [])) a []) \<and>
       (let m = length (snd pr); js' = drop m js; fs' = (if m \<le> length js then fs else drop (m - length js) fs) in
        case vhd_s js' fs' of None \<Rightarrow> False
        | Some j\<^sub>0 \<Rightarrow> (case iget (iget (v_go V) j\<^sub>0 (IArray [])) b None of None \<Rightarrow> False
            | Some e \<Rightarrow> vshiftable_s V a n (fst e # js') fs')))
       (iget (v_cp V) j []))\<close>

lemma vhd_s: \<open>vhd_s js fs = vhd (js @ map fst fs)\<close>
  by (cases js; cases fs) auto

lemma vshiftable_s: \<open>vshiftable_s V a n js fs = vshiftable V a n (js @ map fst fs)\<close>
proof (induction n arbitrary: js fs)
  case (Suc n)
  have d: \<open>drop m js @ map fst (if m \<le> length js then fs else drop (m - length js) fs) =
      drop m (js @ map fst fs)\<close> for m
    by (simp add: drop_map)
  show ?case
    unfolding vshiftable_s.simps vshiftable.simps Let_def vhd_s Suc.IH append_Cons d ..
qed simp

lemma vpick_n_Some: \<open>vpick_n V c acts = Some (act, c') \<Longrightarrow> act \<in> set acts \<and> vmstep_n V c act = Some c'\<close>
  by (induction acts) (auto split: option.splits)

lemma vgo_fst: \<open>vgo V e av RA = Some f \<Longrightarrow> fst f = fst e\<close>
  by (auto simp: vgo_def Let_def split: prod.splits if_splits)

lemma vadv_vshiftable:
  assumes \<open>vadv V (fs, [(a, r)]) = Some c'\<close>
  shows \<open>vshiftable V a n (map fst fs)\<close>
proof -
  have \<open>V = V \<longrightarrow> (\<forall>fs'. (fs, [(a, r)]) = (fs', [(a, r)]) \<longrightarrow> (\<forall>n. vshiftable V a n (map fst fs')))\<close>
  proof (rule vadv.raw_induct[OF _ assms, where P = \<open>\<lambda>V' x y. V' = V \<longrightarrow>
      (\<forall>fs. x = (fs, [(a, r)]) \<longrightarrow> (\<forall>n. vshiftable V a n (map fst fs)))\<close>], goal_cases)
    case (1 adv V' x y)
    show ?case
    proof (intro impI allI)
      fix fs n
      assume V': \<open>V' = V\<close> and x: \<open>x = (fs, [(a, r)])\<close>
      show \<open>vshiftable V a n (map fst fs)\<close>
      proof (cases n)
        case (Suc n')
        from 1(2) V' x obtain j av fs\<^sub>1 act c\<^sub>1 where fs: \<open>fs = (j, av) # fs\<^sub>1\<close>
          and pk: \<open>vpick_n V x (vcands_n V j av [(a, r)]) = Some (act, c\<^sub>1)\<close>
          and rest: \<open>(case act of VShift \<Rightarrow> Some c\<^sub>1 | VReduce _ _ _ \<Rightarrow> adv V c\<^sub>1) = Some y\<close>
          by (auto split: list.splits option.splits prod.splits)
        from vpick_n_Some[OF pk] have mem: \<open>act \<in> set (vcands_n V j av [(a, r)])\<close>
          and st: \<open>vmstep_n V x act = Some c\<^sub>1\<close> by auto
        show ?thesis
        proof (cases act)
          case VShift
          with st x fs show ?thesis
            by (auto simp: Suc vmstep_n_def split: option.splits)
        next
          case (VReduce s b pr)
          from mem VReduce obtain \<tau> where cp: \<open>(s, b, pr) \<in> set (iget (v_cp V) j [])\<close>
            and cl: \<open>(s, \<tau>) \<in> set (iget (iget (v_cl V) j (IArray [])) a [])\<close>
            by (auto simp: vcands_n_def vlic_n_def Let_def list_ex_iff)
          have h: \<open>(case drop (length (snd pr)) fs of [] \<Rightarrow> None
              | (j\<^sub>0, av\<^sub>0) # _ \<Rightarrow> (case iget (iget (v_go V) j\<^sub>0 (IArray [])) b None of None \<Rightarrow> None
                 | Some e \<Rightarrow> map_option (\<lambda>f. (f # drop (length (snd pr)) fs, [(a, r)])) (vgo V e av\<^sub>0 (getR av s)))) =
              Some c\<^sub>1\<close>
            using st unfolding x VReduce vmstep_n_def Let_def fs by simp
          obtain j\<^sub>0 av\<^sub>0 fs\<^sub>0 where dr: \<open>drop (length (snd pr)) fs = (j\<^sub>0, av\<^sub>0) # fs\<^sub>0\<close>
            using h by (cases \<open>drop (length (snd pr)) fs\<close>) auto
          obtain e where go: \<open>iget (iget (v_go V) j\<^sub>0 (IArray [])) b None = Some e\<close>
            using h dr by (auto split: option.splits)
          obtain f where g: \<open>vgo V e av\<^sub>0 (getR av s) = Some f\<close>
            and c1: \<open>c\<^sub>1 = (f # (j\<^sub>0, av\<^sub>0) # fs\<^sub>0, [(a, r)])\<close>
            using h dr go by auto
          from rest VReduce have \<open>adv V c\<^sub>1 = Some y\<close> by simp
          from 1(1)[OF this] c1 have \<open>vshiftable V a n' (map fst (f # (j\<^sub>0, av\<^sub>0) # fs\<^sub>0))\<close> by blast
          then have ih: \<open>vshiftable V a n' (fst e # j\<^sub>0 # map fst fs\<^sub>0)\<close>
            using vgo_fst[OF g] by simp
          have dm: \<open>drop (length (snd pr)) (map fst fs) = j\<^sub>0 # map fst fs\<^sub>0\<close>
            using dr by (simp add: drop_map)
          have mf: \<open>map fst fs = j # map fst fs\<^sub>1\<close> by (simp add: fs)
          show ?thesis
            unfolding Suc vshiftable.simps mf[symmetric]
            using cp cl go ih dm mf by (fastforce simp: list_ex_iff Let_def)
        qed
      qed simp
    qed
  qed
  then show ?thesis by simp
qed

lemma vadv_None: \<open>\<not> vshiftable V a n (map fst fs) \<Longrightarrow> vadv V (fs, [(a, r)]) = None\<close>
  using vadv_vshiftable by fastforce

definition vops :: \<open>('n, 't) vtab \<Rightarrow> (vcfg, 't) rops\<close> where
  \<open>vops V =
     \<lparr>ro_adv = \<lambda>c x. vadv V (fst c, [(vnum V (fst x), snd x)]),
      ro_end = \<lambda>c. vtry V c None,
      ro_pop = \<lambda>c. (case fst c of _ # g # gs \<Rightarrow> Some (g # gs, snd c) | _ \<Rightarrow> None),
      ro_cols = \<lambda>c. col_reps (concat (map (\<lambda>(j, av). concat (map irep_ends av)) (fst c))),
      ro_can = \<lambda>c t. vshiftable_s V (vnum V t) 32 [] (fst c)\<rparr>\<close>

definition vrstop :: \<open>('n, 't) vtab \<Rightarrow> ('n, 't) stab \<Rightarrow> ('n, 't) sitem list \<Rightarrow> ('n, 't) sitem list \<Rightarrow>
    nat \<Rightarrow> 't list \<Rightarrow> ('t, 'ch, 'm) rmode \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow>
    (('n, 't, 'ch, 'm) perr \<times> (('m, 'ch, 't) tword \<times> nat \<times> nat) option) option\<close> where
  \<open>vrstop V T kin kcl i\<^sub>0 ts rm b w =
     (let st = ([v_av0 V], vtcols V w, w, [])
      in (case vdrun V st st of
            Some (VDone _) \<Rightarrow> None
          | Some (VStuck s sh) \<Rightarrow> (case sh of (fs, u, v, tstk) \<Rightarrow>
              Some (rfix (vops V) rm ts b w (length w - length v) (fs, []) tstk
                      (vperr V ts (length w) s sh)))
          | _ \<Rightarrow> srstop T kin kcl i\<^sub>0 ts rm b w))\<close>

text \<open>The same with the tokens numbered by \<open>f\<close>, as \<^const>\<open>vkdiag_f\<close>: the search
  numbers a token at every step it tries, and the stop the whole word per round.\<close>

definition vops_f :: \<open>('n, 't) vtab \<Rightarrow> ('t \<Rightarrow> nat) \<Rightarrow> (vcfg, 't) rops\<close> where
  \<open>vops_f V f =
     \<lparr>ro_adv = \<lambda>c x. vadv V (fst c, [(f (fst x), snd x)]),
      ro_end = \<lambda>c. vtry_f V f c None,
      ro_pop = \<lambda>c. (case fst c of _ # g # gs \<Rightarrow> Some (g # gs, snd c) | _ \<Rightarrow> None),
      ro_cols = \<lambda>c. col_reps (concat (map (\<lambda>(j, av). concat (map irep_ends av)) (fst c))),
      ro_can = \<lambda>c t. vshiftable_s V (f t) 32 [] (fst c)\<rparr>\<close>

definition vrstop_f :: \<open>('n, 't) vtab \<Rightarrow> ('t \<Rightarrow> nat) \<Rightarrow> ('n, 't) stab \<Rightarrow> ('n, 't) sitem list \<Rightarrow>
    ('n, 't) sitem list \<Rightarrow> nat \<Rightarrow> 't list \<Rightarrow> ('t, 'ch, 'm) rmode \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow>
    (('n, 't, 'ch, 'm) perr \<times> (('m, 'ch, 't) tword \<times> nat \<times> nat) option) option\<close> where
  \<open>vrstop_f V f T kin kcl i\<^sub>0 ts rm b w =
     (let st = ([v_av0 V], vtnum f w, w, [])
      in (case vdrun V st st of
            Some (VDone _) \<Rightarrow> None
          | Some (VStuck s sh) \<Rightarrow> (case sh of (fs, u, v, tstk) \<Rightarrow>
              Some (rfix (vops_f V f) rm ts b w (length w - length v) (fs, []) tstk
                      (vperr_f V f ts (length w) s sh)))
          | _ \<Rightarrow> srstop T kin kcl i\<^sub>0 ts rm b w))\<close>

lemma vops_f_vnum: \<open>vops_f V (vnum V) = vops V\<close>
  by (simp add: vops_f_def vops_def vtry_f_vnum)

lemma vops_f_can: \<open>\<not> ro_can (vops_f V f) c t \<Longrightarrow> ro_adv (vops_f V f) c (t, r) = None\<close>
  by (simp add: vops_f_def vshiftable_s vadv_None)

lemma vrstop_f_eq: \<open>vnum V = f \<Longrightarrow> vrstop V = vrstop_f V f\<close>
  by (hypsubst, unfold vrstop_f_def vrstop_def vops_f_vnum vperr_f_vnum vtcols_vtnum) (rule refl)

subsection \<open>The diagnostics of a grammar with error productions\<close>

text \<open>The error token is not offered to the user: it is left out of the candidates
  for the expected terminals, and the messages summarise them over the grammar
  without the productions that use it.\<close>

definition no_err :: \<open>'t \<Rightarrow> ('n, 't) is_cfg \<Rightarrow> ('n, 't) is_cfg\<close> where
  \<open>no_err e G = G\<lparr>iprods := filter (\<lambda>(A, rhs). Tm e \<notin> fst ` set rhs) (iprods G)\<rparr>\<close>

subsection \<open>Trees without error nodes\<close>

text \<open>The terminals at the leaves of a tree. An error node is a node with a leaf of
  the error token.\<close>

fun atoks :: \<open>('m, 'ch, 'n, 't) ast \<Rightarrow> 't list\<close> where
  \<open>atoks (Leaf x) = [tok x]\<close>
| \<open>atoks (Node n ts) = concat (map atoks ts)\<close>

lemma atoks_erase: \<open>atoks (erase pt) = map tok (pyield pt)\<close>
  by (induction pt) (simp_all add: map_concat comp_def cong: map_cong)

lemma recover_no_error_generic:
  assumes body: \<open>parse_fn = (\<lambda>w. Option.bind (dparse G Shn w) dec)\<close>
    and fn: \<open>fresh_name G Shn\<close>
    and rec: \<open>parse_fn w = Some x\<close>
    and none: \<open>\<forall>y \<in> set w. tok y \<noteq> e\<close>
  shows \<open>\<exists>t. dec t = Some x \<and> ast_of G (Nt (istart G)) (istart_ind G) t w \<and> e \<notin> set (atoks t)\<close>
proof -
  from rec body obtain t where p: \<open>dparse G Shn w = Some t\<close> and d: \<open>dec t = Some x\<close>
    by (auto simp: bind_eq_Some_conv)
  from dparse_sound_ast[OF fn p] have a: \<open>ast_of G (Nt (istart G)) (istart_ind G) t w\<close> .
  then obtain pt where \<open>erase pt = t\<close> \<open>pyield pt = w\<close>
    unfolding ast_of_def by blast
  with atoks_erase[of pt] none have \<open>e \<notin> set (atoks t)\<close> by auto
  with a d show ?thesis by blast
qed

end
