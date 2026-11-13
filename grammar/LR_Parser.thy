(* Author: Basil Fürer, Dmitriy Traytel, Claude *)

theory LR_Parser
  imports TIGER_Grammar.LR_Plain TIGER_Grammar.LR_Sparse TIGER_Grammar.LR_Vec TIGER_Grammar.LR_Diag TIGER_Grammar.LR_Recover Grammar_Command
  keywords "parser_error_states" :: diag
begin

section \<open>Parser-facing theorems: \<open>dparse\<close> composed with a decoder\<close>

text \<open>The backend (\<^text>\<open>Grammar_Command\<close>) defines each generated parser
  as \<open>\<lambda>w. Option.bind (dparse G Shn w) dec\<close>, where \<open>dec\<close> maps the raw
  \<open>ast\<close> to the grammar's carrier type.  Soundness of the composition is
  unconditional modulo \<^const>\<open>fresh_name\<close> (discharged by construction of
  \<open>Shn\<close>); completeness additionally needs \<^const>\<open>mdet\<close>
  \<^cite>\<open>\<open>Thm.~5.4.4\<close> in "barthwal2010-thesis-cfl-hol4"\<close> \<^cite>\<open>\<open>Thm.~3\<close> in "jourdan2012-validating-lr1"\<close>, which
  \<^text>\<open>rlalr_sufficient\<close> reduces to \<^emph>\<open>evaluation\<close> of the static
  check \<^const>\<open>rlalr_conflicts\<close>, so the emitted \<open>.complete\<close> theorem is
  hypothesis-free whenever the check computes \<open>[]\<close>.\<close>

theorem dparse_bind_sound:
  assumes fn: \<open>fresh_name G Shn\<close>
    and rec: \<open>Option.bind (dparse G Shn w) dec = Some x\<close>
  shows \<open>w \<in> ilang G\<close>
proof (cases \<open>dparse G Shn w\<close>)
  case None with rec show ?thesis by simp
next
  case (Some t) show ?thesis using dparse_sound[OF fn Some] .
qed

theorem dparse_bind_complete:
  assumes fn: \<open>fresh_name G Shn\<close>
    and det: \<open>mdet G Shn\<close>
    and mem: \<open>w \<in> ilang G\<close>
    and dec_total: \<open>\<And>t. ast_of G (Nt (istart G)) (istart_ind G) t w \<Longrightarrow>
                         \<exists>x. dec t = Some x\<close>
  shows \<open>\<exists>x. Option.bind (dparse G Shn w) dec = Some x\<close>
proof -
  from dparse_complete_lang[OF fn det mem] obtain t where
      parsed: \<open>dparse G Shn w = Some t\<close>
    and ao: \<open>ast_of G (Nt (istart G)) (istart_ind G) t w\<close> by blast
  from dec_total[OF ao] obtain x where \<open>dec t = Some x\<close> by blast
  with parsed show ?thesis by simp
qed

theorem dparse_bind:
  assumes fn: \<open>fresh_name G Shn\<close> and det: \<open>mdet G Shn\<close>
    and dec_total: \<open>\<And>t. ast_of G (Nt (istart G)) (istart_ind G) t w \<Longrightarrow>
                        \<exists>x. dec t = Some x\<close>
  shows \<open>w \<in> ilang G \<longleftrightarrow> (\<exists>x. Option.bind (dparse G Shn w) dec = Some x)\<close>
proof
  assume \<open>w \<in> ilang G\<close>
  from dparse_bind_complete[OF fn det this dec_total] show
    \<open>\<exists>x. Option.bind (dparse G Shn w) dec = Some x\<close> .
next
  assume \<open>\<exists>x. Option.bind (dparse G Shn w) dec = Some x\<close>
  then obtain x where \<open>Option.bind (dparse G Shn w) dec = Some x\<close> ..
  from dparse_bind_sound[OF fn this] show \<open>w \<in> ilang G\<close> .
qed

subsection \<open>Schematic forms for the backend's \<^text>\<open>define\<close>\<close>

lemma dparse_sound_generic:
  assumes body: \<open>parse_fn = (\<lambda>w. Option.bind (dparse G Shn w) dec)\<close>
    and fn:   \<open>fresh_name G Shn\<close>
    and rec:  \<open>parse_fn w = Some x\<close>
  shows \<open>w \<in> ilang G\<close>
  by (metis body fn rec dparse_bind_sound)

lemma dparse_complete_generic:
  assumes body: \<open>parse_fn = (\<lambda>w. Option.bind (dparse G Shn w) dec)\<close>
    and fn:   \<open>fresh_name G Shn\<close>
    and det:  \<open>mdet G Shn\<close>
    and mem:  \<open>w \<in> ilang G\<close>
    and dec_total: \<open>\<And>t. ast_of G (Nt (istart G)) (istart_ind G) t w \<Longrightarrow>
                         \<exists>x. dec t = Some x\<close>
  shows \<open>\<exists>x. parse_fn w = Some x\<close>
  using body dparse_bind_complete[OF fn det mem dec_total] by simp

section \<open>Exact completeness: the driver returns the erasure of the tree\<close>

text \<open>\<^text>\<open>dparse_complete\<close> only says that the driver returns \<^emph>\<open>some\<close> tree
  of the word.  Relating a generated parser to the relation family of
  \<^theory_text>\<open>grammar (relation)\<close> needs more: the tree it returns must be the
  erasure of the tree the relation exhibits, i.e.\ the word must have a
  unique parse.  \<^const>\<open>mdet\<close> does not give this.  The conflict report
  ignores the start production, so a configuration that \<^emph>\<open>accepts\<close> may
  still license a live reduce: a cycle \<open>S \<Rightarrow>⁺ S\<close> through the start symbol,
  where the driver stops at the first accepting configuration and a second
  tree continues.  \<^text>\<open>acc_conflicts\<close> is the missing static check: an
  LR(0) state holding the completed start item together with an
  end-of-input reduce cell of another production.  Together with
  \<^const>\<open>mdet\<close> it pins the driver's answer to \<^term>\<open>erase pt\<close>
  (\<^text>\<open>dparse_complete_exact\<close>), and every parse tree of a word erases to
  the same ast (\<^text>\<open>ast_of_unique\<close>).

  The uniqueness argument is that of Jourdan et al.
  \<^cite>\<open>\<open>Sect.~3.4, Thm.~4\<close> in "jourdan2012-validating-lr1"\<close>: the driver is a function, and
  by completeness it returns the value of each of two parses, so the two agree.  Barthwal
  \<^cite>\<open>\<open>Sect.~5.4.5, Thm.~5.4.5\<close> in "barthwal2010-thesis-cfl-hol4"\<close> proves that a grammar
  whose SLR machine is built without conflicts is unambiguous.  Here uniqueness holds up
  to erasure: two trees of a word give the same ast.\<close>

subsection \<open>The tree stack along an action list\<close>

text \<open>The tree-stack component of the driver depends only on the actions
  taken: a shift pushes the leaf of the next token, a reduce folds the
  right-hand side.  Along the trace of a tree it builds the tree's erasure.\<close>

fun tsteps :: \<open>('n, 't) dact list \<Rightarrow> ('m, 'ch, 't) tword \<times> ('m, 'ch, 'n, 't) ast list \<Rightarrow>
    (('m, 'ch, 't) tword \<times> ('m, 'ch, 'n, 't) ast list) option\<close> where
  \<open>tsteps [] s = Some s\<close>
| \<open>tsteps (DShift # acts) (v, tstk) =
     (case v of [] \<Rightarrow> None | t # v' \<Rightarrow> tsteps acts (v', Leaf t # tstk))\<close>
| \<open>tsteps (DReduce pr # acts) (v, tstk) =
     tsteps acts (v, Node (fst pr) (rev (take (length (snd pr)) tstk))
                     # drop (length (snd pr)) tstk)\<close>

lemma tsteps_append:
  \<open>tsteps (as @ bs) s = (case tsteps as s of None \<Rightarrow> None | Some s' \<Rightarrow> tsteps bs s')\<close>
  by (induction as s rule: tsteps.induct) (auto split: list.splits)

lemma tsteps_concat:
  assumes \<open>list_all2 (\<lambda>pt tr. \<forall>rest tstk.
      tsteps tr (pyield pt @ rest, tstk) = Some (rest, erase pt # tstk)) pts trs\<close>
  shows \<open>tsteps (concat trs) (concat (map pyield pts) @ rest, tstk) =
           Some (rest, rev (map erase pts) @ tstk)\<close>
  using assms
proof (induction arbitrary: rest tstk rule: list_all2_induct)
  case Nil show ?case by simp
next
  case (Cons pt pts tr trs)
  show ?case
    unfolding concat.simps list.map(2) tsteps_append append_assoc
    using Cons.hyps(1)[rule_format, of \<open>concat (map pyield pts) @ rest\<close> tstk] Cons.IH by simp
qed

lemma tsteps_mtrace:
  \<open>mtrace G pt acts \<Longrightarrow> tsteps acts (pyield pt @ rest, tstk) = Some (rest, erase pt # tstk)\<close>
proof (induction arbitrary: rest tstk rule: mtrace.induct)
  case (mt_leaf t) show ?case by simp
next
  case (mt_node A rhs i pts trs)
  have kids: \<open>list_all2 (\<lambda>pt tr. \<forall>rest tstk.
      tsteps tr (pyield pt @ rest, tstk) = Some (rest, erase pt # tstk)) pts trs\<close>
    using mt_node.IH by (rule list_all2_mono) blast
  have lenp: \<open>length pts = length rhs\<close> using mt_node.hyps(2) by (simp add: list_all2_lengthD)
  show ?case
    by (simp add: tsteps_append tsteps_concat[OF kids] lenp)
qed

subsection \<open>One step of the driver, along the trace\<close>

text \<open>\<^text>\<open>dstep_of_imstep_exact\<close> in terms of \<^const>\<open>tsteps\<close>: the shift
  case has input left, since the machine shifted.\<close>

lemma dstep_exact:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and stc: \<open>sts = pr0_states G Shn\<close>
    and gtc: \<open>gt = pgtab G sts\<close>
    and Lc: \<open>L = la_fix G Shn\<close>
    and rt: \<open>redtab = red_buckets G Shn (length sts)\<close>
    and det: \<open>mdet G Shn\<close>
    and ireach: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close>
    and inv: \<open>dfollow_ok G sts ((Xs, w), cstk, istk, v, tstk)\<close>
    and step: \<open>imstep G gt sts ((Xs, w), istk) act = Some (gc', istk')\<close>
    and live: \<open>dlive gc'\<close>
    and lic: \<open>\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts ((Xs, w), istk) pr\<close>
  shows \<open>act \<in> set (dcands G (hd istk) (redtab ! hd istk) (xclosure_auto G (hd Xs)) (Xs, w)) \<and>
         (\<exists>v' tstk'. tsteps [act] (v, tstk) = Some (v', tstk') \<and>
            dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk)
              = Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk') \<and>
            dfollow_ok G sts (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk'))\<close>
proof -
  from dstep_of_imstep_exact[OF assms] obtain v' tstk' where
      cand: \<open>act \<in> set (dcands G (hd istk) (redtab ! hd istk) (xclosure_auto G (hd Xs)) (Xs, w))\<close>
    and ts: \<open>(v', tstk') = tstep act (v, tstk)\<close>
    and ds: \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk)
              = Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')\<close>
    and inv': \<open>dfollow_ok G sts (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')\<close>
    by blast
  have v_ne: \<open>v \<noteq> []\<close> if sh: \<open>act = DShift\<close>
  proof -
    have \<open>w = tcols v\<close> using inv unfolding dfollow_ok_def by simp
    moreover have \<open>w \<noteq> []\<close>
      using step unfolding sh imstep_def mstep_def mstep_cached_def
      by (auto split: list.splits)
    ultimately show \<open>v \<noteq> []\<close> by auto
  qed
  have \<open>tsteps [act] (v, tstk) = Some (v', tstk')\<close>
    using ts v_ne by (cases act) (auto split: list.splits)
  with cand ds inv' show ?thesis by blast
qed

subsection \<open>The driver follows the trace without stopping early\<close>

lemma dsteps_trace:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and stc: \<open>sts = pr0_states G Shn\<close>
    and gtc: \<open>gt = pgtab G sts\<close>
    and Lc: \<open>L = la_fix G Shn\<close>
    and rt: \<open>redtab = red_buckets G Shn (length sts)\<close>
    and det: \<open>mdet G Shn\<close> and fn: \<open>fresh_name G Shn\<close> and chk: \<open>acc_conflicts G Shn = []\<close>
  shows \<open>mdrive G gt sts L acts (gc, istk) \<Longrightarrow> imreach G Shn gt sts (gc, istk) \<Longrightarrow>
     dfollow_ok G sts (gc, cstk, istk, v, tstk) \<Longrightarrow> dinv G Shn w (gc, cstk, istk, v, tstk) \<Longrightarrow>
     tsteps acts (v, tstk) = Some (v', tstk') \<Longrightarrow>
     (\<forall>k < length acts. \<exists>st\<^sub>k. dsteps G gt sts redtab k (gc, cstk, istk, v, tstk) = Some st\<^sub>k \<and>
         \<not> gfinal G Shn (fst st\<^sub>k)) \<and>
     (\<exists>gc'. mrun G acts gc = Some gc' \<and>
        (\<exists>istk'. dsteps G gt sts redtab (length acts) (gc, cstk, istk, v, tstk)
          = Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')))\<close>
proof (induction acts arbitrary: gc istk cstk v tstk)
  case Nil
  have \<open>cstk = map (xclosure_auto G) (fst gc)\<close>
    using Nil.prems(3) unfolding dfollow_ok_def by (cases gc) simp
  then show ?case using Nil.prems(5) by auto
next
  case (Cons act acts)
  obtain Xs u where gc: \<open>gc = (Xs, u)\<close> by (cases gc)
  from mdrive_ConsD[OF Cons.prems(1)] obtain ic\<^sub>1 where
      st\<^sub>0: \<open>imstep G gt sts (gc, istk) act = Some ic\<^sub>1\<close> and lv\<^sub>0: \<open>dlive (fst ic\<^sub>1)\<close>
    and lc\<^sub>0: \<open>\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts (gc, istk) pr\<close>
    and rest\<^sub>0: \<open>mdrive G gt sts L acts ic\<^sub>1\<close> by blast
  obtain gc\<^sub>1 istk\<^sub>1 where ic\<^sub>1: \<open>ic\<^sub>1 = (gc\<^sub>1, istk\<^sub>1)\<close> by (cases ic\<^sub>1)
  have st: \<open>imstep G gt sts ((Xs, u), istk) act = Some (gc\<^sub>1, istk\<^sub>1)\<close>
    using st\<^sub>0 gc ic\<^sub>1 by simp
  have lv: \<open>dlive gc\<^sub>1\<close> using lv\<^sub>0 ic\<^sub>1 by simp
  have lc: \<open>\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts ((Xs, u), istk) pr\<close>
    using lc\<^sub>0 gc by simp
  have ireach: \<open>imreach G Shn gt sts ((Xs, u), istk)\<close> using Cons.prems(2) gc by simp
  have inv: \<open>dfollow_ok G sts ((Xs, u), cstk, istk, v, tstk)\<close>
    using Cons.prems(3) gc by simp
  from dstep_exact[OF tab stc gtc Lc rt det ireach inv st lv lc] obtain v\<^sub>1 tstk\<^sub>1 where
      cand: \<open>act \<in> set (dcands G (hd istk) (redtab ! hd istk) (xclosure_auto G (hd Xs)) (Xs, u))\<close>
    and ts\<^sub>1: \<open>tsteps [act] (v, tstk) = Some (v\<^sub>1, tstk\<^sub>1)\<close>
    and ds: \<open>dstep G gt sts redtab ((Xs, u), cstk, istk, v, tstk) =
            Some (gc\<^sub>1, map (xclosure_auto G) (fst gc\<^sub>1), istk\<^sub>1, v\<^sub>1, tstk\<^sub>1)\<close>
    and inv\<^sub>1: \<open>dfollow_ok G sts (gc\<^sub>1, map (xclosure_auto G) (fst gc\<^sub>1), istk\<^sub>1, v\<^sub>1, tstk\<^sub>1)\<close>
    by blast
  have ms: \<open>mstep G gc act = Some gc\<^sub>1\<close>
    using imstep_mstep[of G gt sts \<open>(gc, istk)\<close> act ic\<^sub>1] st\<^sub>0 ic\<^sub>1 by simp
  have notfin: \<open>\<not> gfinal G Shn (Xs, u)\<close>
  proof
    assume fin: \<open>gfinal G Shn (Xs, u)\<close>
    then have u: \<open>u = []\<close> unfolding gfinal_def by simp
    obtain pr where act: \<open>act = DReduce pr\<close>
    proof (cases act)
      case DShift
      with ms u have False unfolding mstep_def mstep_cached_def gc by simp
      then show ?thesis ..
    qed
    have ok: \<open>didx_ok G (pr0_states G Shn) Xs istk\<close>
      using Cons.prems(3) gc stc unfolding dfollow_ok_def by simp
    show False
      by (rule no_reduce_at_final[OF fn chk Cons.prems(4)[unfolded gc] ok fin
            cand[unfolded act rt stc] ms[unfolded gc act] lv])
  qed
  have dinv\<^sub>1: \<open>dinv G Shn w (gc\<^sub>1, map (xclosure_auto G) (fst gc\<^sub>1), istk\<^sub>1, v\<^sub>1, tstk\<^sub>1)\<close>
    by (rule dstep_inv[OF fn Cons.prems(4)[unfolded gc] ds])
  have ireach\<^sub>1: \<open>imreach G Shn gt sts (gc\<^sub>1, istk\<^sub>1)\<close>
    using imreach_step[OF Cons.prems(2) st\<^sub>0 lv\<^sub>0] ic\<^sub>1 by simp
  have rest: \<open>mdrive G gt sts L acts (gc\<^sub>1, istk\<^sub>1)\<close> using rest\<^sub>0 ic\<^sub>1 by simp
  have ts_rest: \<open>tsteps acts (v\<^sub>1, tstk\<^sub>1) = Some (v', tstk')\<close>
    using Cons.prems(5) ts\<^sub>1 tsteps_append[of \<open>[act]\<close> acts \<open>(v, tstk)\<close>] by simp
  from Cons.IH[OF rest ireach\<^sub>1 inv\<^sub>1 dinv\<^sub>1 ts_rest] obtain gc' istk' where
      nf: \<open>\<forall>k < length acts. \<exists>st\<^sub>k. dsteps G gt sts redtab k
            (gc\<^sub>1, map (xclosure_auto G) (fst gc\<^sub>1), istk\<^sub>1, v\<^sub>1, tstk\<^sub>1) = Some st\<^sub>k \<and>
            \<not> gfinal G Shn (fst st\<^sub>k)\<close>
    and mr: \<open>mrun G acts gc\<^sub>1 = Some gc'\<close>
    and dr: \<open>dsteps G gt sts redtab (length acts)
              (gc\<^sub>1, map (xclosure_auto G) (fst gc\<^sub>1), istk\<^sub>1, v\<^sub>1, tstk\<^sub>1) =
                Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')\<close>
    by blast
  have ds': \<open>dstep G gt sts redtab (gc, cstk, istk, v, tstk) =
      Some (gc\<^sub>1, map (xclosure_auto G) (fst gc\<^sub>1), istk\<^sub>1, v\<^sub>1, tstk\<^sub>1)\<close>
    using ds gc by simp
  have A: \<open>\<forall>k < length (act # acts). \<exists>st\<^sub>k.
      dsteps G gt sts redtab k (gc, cstk, istk, v, tstk) = Some st\<^sub>k \<and> \<not> gfinal G Shn (fst st\<^sub>k)\<close>
  proof (intro allI impI)
    fix k assume k: \<open>k < length (act # acts)\<close>
    show \<open>\<exists>st\<^sub>k. dsteps G gt sts redtab k (gc, cstk, istk, v, tstk) = Some st\<^sub>k \<and>
        \<not> gfinal G Shn (fst st\<^sub>k)\<close>
    proof (cases k)
      case 0
      then show ?thesis using notfin gc by simp
    next
      case (Suc k')
      then have \<open>k' < length acts\<close> using k by simp
      then show ?thesis
        using nf[rule_format, of k'] unfolding Suc dsteps_Suc_step[OF ds'] by simp
    qed
  qed
  have B: \<open>mrun G (act # acts) gc = Some gc'\<close> using ms mr by simp
  have C: \<open>dsteps G gt sts redtab (Suc (length acts)) (gc, cstk, istk, v, tstk) =
      Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')\<close>
    unfolding dsteps_Suc_step[OF ds'] by (rule dr)
  from A B C show ?case by auto
qed

lemma drun\<^sub>w\<^sub>f_of_dsteps:
  \<open>dsteps G gt sts redtab n st = Some st' \<Longrightarrow>
   (\<forall>k < n. \<exists>st\<^sub>k. dsteps G gt sts redtab k st = Some st\<^sub>k \<and> \<not> gfinal G Shn (fst st\<^sub>k)) \<Longrightarrow>
   gfinal G Shn (fst st') \<Longrightarrow>
   (case st' of (gc, cstk, istk, v, tstk) \<Rightarrow> tstk) = t # rest \<Longrightarrow>
   drun\<^sub>w\<^sub>f G Shn gt sts redtab st = Some t\<close>
  by (rule drun_imp_drun\<^sub>w\<^sub>f[OF drun_of_dsteps])

subsection \<open>The licensed run of a tree, from the root\<close>

subsection \<open>Exact completeness and uniqueness of the parse\<close>

theorem dparse_complete_exact:
  assumes fn: \<open>fresh_name G Shn\<close> and det: \<open>mdet G Shn\<close> and chk: \<open>acc_conflicts G Shn = []\<close>
    and wf: \<open>wf_ptree G pt\<close> and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
  shows \<open>dparse G Shn (pyield pt) = Some (erase pt)\<close>
proof -
  let ?sts = \<open>pr0_states G Shn\<close> and ?gt = \<open>pgtab G (pr0_states G Shn)\<close>
  let ?L = \<open>la_fix G Shn\<close> and ?i\<^sub>0 = \<open>st_find (pr0_states G Shn) (lr0_start G Shn)\<close>
  let ?redtab = \<open>red_buckets G Shn (length (pr0_states G Shn))\<close>
  let ?w = \<open>pyield pt\<close>
  let ?st = \<open>(([xinit G Shn], tcols ?w), [xclosure_auto G (xinit G Shn)], [?i\<^sub>0], ?w,
             [] :: ('m, 'ch, 'n, 't) ast list)\<close>
  have tab: \<open>tables_ok G Shn ?sts ?gt ?L\<close> by (rule tables_ok_concrete)
  from mtrace_ex[OF wf] obtain acts where tr: \<open>mtrace G pt acts\<close> by blast
  have drv: \<open>mdrive G ?gt ?sts ?L acts (([xinit G Shn], tcols ?w), [?i\<^sub>0])\<close>
    by (rule mdrive_root[OF wf rt tr])
  have fin: \<open>mcompletes G Shn acts ([xinit G Shn], tcols ?w)\<close>
    by (rule mtrace_completes[OF wf tr rt])
  have inv: \<open>dfollow_ok G ?sts ?st\<close>
    using dfollow_ok_dinit[of G Shn ?w] unfolding dinit_def .
  have dinv: \<open>dinv G Shn ?w ?st\<close>
    using dinv_init[of G Shn ?w ?sts] unfolding dinit_def .
  have ts: \<open>tsteps acts (?w, []) = Some ([], [erase pt])\<close>
    using tsteps_mtrace[OF tr, of \<open>[]\<close> \<open>[]\<close>] by simp
  from dsteps_trace[OF tab refl refl refl refl det fn chk drv imreach_init inv dinv ts]
  obtain gc' istk' where
      nf: \<open>\<forall>k < length acts. \<exists>st\<^sub>k. dsteps G ?gt ?sts ?redtab k ?st = Some st\<^sub>k \<and>
             \<not> gfinal G Shn (fst st\<^sub>k)\<close>
    and mr: \<open>mrun G acts ([xinit G Shn], tcols ?w) = Some gc'\<close>
    and ds: \<open>dsteps G ?gt ?sts ?redtab (length acts) ?st =
             Some (gc', map (xclosure_auto G) (fst gc'), istk', [], [erase pt])\<close> by blast
  have gf: \<open>gfinal G Shn gc'\<close> using fin mr unfolding mcompletes_def by simp
  have \<open>drun\<^sub>w\<^sub>f G Shn ?gt ?sts ?redtab ?st = Some (erase pt)\<close>
    by (rule drun\<^sub>w\<^sub>f_of_dsteps[OF ds nf]) (use gf in simp_all)
  then show ?thesis unfolding dparse_def dinit_def Let_def by simp
qed

corollary ast_of_unique:
  assumes fn: \<open>fresh_name G Shn\<close> and det: \<open>mdet G Shn\<close> and chk: \<open>acc_conflicts G Shn = []\<close>
    and a: \<open>ast_of G (Nt (istart G)) (istart_ind G) t w\<close>
    and b: \<open>ast_of G (Nt (istart G)) (istart_ind G) t' w\<close>
  shows \<open>t = t'\<close>
proof -
  from a obtain pt where \<open>wf_ptree G pt\<close> \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    \<open>erase pt = t\<close> \<open>pyield pt = w\<close> unfolding ast_of_def by blast
  then have 1: \<open>dparse G Shn w = Some t\<close> using dparse_complete_exact[OF fn det chk] by blast
  from b obtain pt' where \<open>wf_ptree G pt'\<close> \<open>proot pt' = (Nt (istart G), istart_ind G)\<close>
    \<open>erase pt' = t'\<close> \<open>pyield pt' = w\<close> unfolding ast_of_def by blast
  then have 2: \<open>dparse G Shn w = Some t'\<close> using dparse_complete_exact[OF fn det chk] by blast
  from 1 2 show ?thesis by simp
qed

subsection \<open>Parser-facing forms: the relation family\<close>

text \<open>For \<^theory_text>\<open>grammar (relation)\<close> the backend states soundness and
  completeness against the relation \<open>P\<close> of the start symbol.  The two
  \<open>bridge\<close> premises are per-grammar lemmas proved at parser-definition
  time (\<^file>\<open>parser_rel_bridge.ML\<close>): a decoded value satisfies the relation, and
  the relation exhibits a tree the decoder maps to the value.\<close>

lemma dparse_rel_sound_generic:
  assumes body: \<open>parse_fn = (\<lambda>w. Option.bind (dparse G Shn w) dec)\<close>
    and fn: \<open>fresh_name G Shn\<close>
    and bridge: \<open>\<And>pt x. wf_ptree G pt \<Longrightarrow> proot pt = (Nt (istart G), istart_ind G) \<Longrightarrow>
                  dec (erase pt) = Some x \<Longrightarrow> P (pyield pt) x\<close>
    and rec: \<open>parse_fn w = Some x\<close>
  shows \<open>P w x\<close>
proof -
  from rec body obtain t where p: \<open>dparse G Shn w = Some t\<close> and d: \<open>dec t = Some x\<close>
    by (auto simp: bind_eq_Some_conv)
  from dparse_sound_ast[OF fn p] obtain pt where
      \<open>wf_ptree G pt\<close> \<open>proot pt = (Nt (istart G), istart_ind G)\<close> \<open>erase pt = t\<close> \<open>pyield pt = w\<close>
    unfolding ast_of_def by blast
  with bridge[of pt x] d show ?thesis by simp
qed

lemma dparse_rel_complete_generic:
  assumes body: \<open>parse_fn = (\<lambda>w. Option.bind (dparse G Shn w) dec)\<close>
    and fn: \<open>fresh_name G Shn\<close>
    and det: \<open>mdet G Shn\<close>
    and chk: \<open>acc_conflicts G Shn = []\<close>
    and bridge: \<open>\<And>w x. P w x \<Longrightarrow> \<exists>pt. wf_ptree G pt \<and> proot pt = (Nt (istart G), istart_ind G) \<and>
                  pyield pt = w \<and> dec (erase pt) = Some x\<close>
    and rel: \<open>P w x\<close>
  shows \<open>parse_fn w = Some x\<close>
proof -
  from bridge[OF rel] obtain pt where wf: \<open>wf_ptree G pt\<close>
    and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close> and y: \<open>pyield pt = w\<close>
    and d: \<open>dec (erase pt) = Some x\<close> by blast
  from dparse_complete_exact[OF fn det chk wf rt] have \<open>dparse G Shn w = Some (erase pt)\<close>
    by (simp add: y)
  with d body show ?thesis by simp
qed

subsection \<open>Parser-facing forms: the tree\<close>

text \<open>For \<^theory_text>\<open>parser (ast)\<close> the decoder is \<^const>\<open>Some\<close>: the parser returns the
  tree of \<^const>\<open>dparse\<close>, and the theorems speak of it. Soundness: the tree is the
  erasure of a parse tree of the word; completeness: the erasure of every parse tree is
  returned for its yield, which also makes the tree unique.\<close>

lemma dparse_ast_sound_generic:
  assumes body: \<open>parse_fn = (\<lambda>w. Option.bind (dparse G Shn w) Some)\<close>
    and fn: \<open>fresh_name G Shn\<close>
    and rec: \<open>parse_fn w = Some t\<close>
  shows \<open>ast_of G (Nt (istart G)) (istart_ind G) t w\<close>
  using rec by (simp add: body dparse_sound_ast[OF fn])

lemma dparse_ast_complete_lang_generic:
  assumes body: \<open>parse_fn = (\<lambda>w. Option.bind (dparse G Shn w) Some)\<close>
    and fn: \<open>fresh_name G Shn\<close>
    and det: \<open>mdet G Shn\<close>
    and mem: \<open>w \<in> ilang G\<close>
  shows \<open>\<exists>t. parse_fn w = Some t\<close>
  by (rule dparse_complete_generic[OF body fn det mem]) simp

lemma dparse_ast_complete_generic:
  assumes body: \<open>parse_fn = (\<lambda>w. Option.bind (dparse G Shn w) Some)\<close>
    and fn: \<open>fresh_name G Shn\<close>
    and det: \<open>mdet G Shn\<close>
    and chk: \<open>acc_conflicts G Shn = []\<close>
    and wf: \<open>wf_ptree G pt\<close>
    and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
  shows \<open>parse_fn (pyield pt) = Some (erase pt)\<close>
  using dparse_complete_exact[OF fn det chk wf rt] by (simp add: body)

lemma recover_no_error_ast_generic:
  assumes body: \<open>parse_fn = (\<lambda>w. Option.bind (dparse G Shn w) Some)\<close>
    and fn: \<open>fresh_name G Shn\<close>
    and rec: \<open>parse_fn w = Some t\<close>
    and none: \<open>\<forall>y \<in> set w. tok y \<noteq> e\<close>
  shows \<open>ast_of G (Nt (istart G)) (istart_ind G) t w \<and> e \<notin> set (atoks t)\<close>
  using recover_no_error_generic[OF body fn rec none] by simp


section \<open>Explaining the reports\<close>

text \<open>Diagnostics for the \<^theory_text>\<open>parser\<close> command, after Menhir's
  \<open>.conflicts\<close> file \<^cite>\<open>\<open>Sect.~6\<close> in "pottier2026-menhir-manual"\<close>: for every pair the checks return, the items of the
  state, a symbol path from the start state with a sample input
  (nonterminals expanded to shortest terminal words), the conflicting
  actions with the column relation each imposes on the lookahead against the
  state's anchor, and a bounded search for an annotated word on which the
  driver has two live candidates, a witness that the ambiguity is real and
  not an over-approximation of the check.  Nothing here enters a proof; the
  checks themselves are untouched.  Productions are reported by their index
  in \<^const>\<open>iprods\<close>, which the command maps back to the source.\<close>

subsection \<open>Shortest terminal words\<close>

fun syms_word :: \<open>('n \<times> 't list) list \<Rightarrow> ('n, 't) sym list \<Rightarrow> 't list option\<close> where
  \<open>syms_word tab [] = Some []\<close>
| \<open>syms_word tab (Tm a # xs) = map_option ((#) a) (syms_word tab xs)\<close>
| \<open>syms_word tab (Nt A # xs) = (case map_of tab A of
     None \<Rightarrow> None | Some w \<Rightarrow> map_option ((@) w) (syms_word tab xs))\<close>

definition mw_step :: \<open>('n, 't) is_cfg \<Rightarrow> ('n \<times> 't list) list \<Rightarrow> ('n \<times> 't list) list\<close> where
  \<open>mw_step G tab = fold (\<lambda>(A, rhs) tab'. case syms_word tab (map fst rhs) of
       None \<Rightarrow> tab'
     | Some w \<Rightarrow> (case map_of tab' A of
         None \<Rightarrow> (A, w) # tab'
       | Some w' \<Rightarrow> if length w < length w' then (A, w) # tab' else tab'))
     (iprods G) tab\<close>

text \<open>A shortest word has a derivation tree of height at most the number of
  nonterminals (a repeated nonterminal on a path can be cut), so this many
  rounds reach the fixpoint.\<close>

definition min_words :: \<open>('n, 't) is_cfg \<Rightarrow> ('n \<times> 't list) list\<close> where
  \<open>min_words G = (mw_step G ^^ Suc (length (iprods G))) []\<close>

subsection \<open>Paths through an automaton\<close>

fun path_bfs :: \<open>('a \<Rightarrow> (('n, 't) sym \<times> 'a) list) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow>
    'a list \<Rightarrow> ('a \<times> ('n, 't) sym list) list \<Rightarrow> ('n, 't) sym list option\<close> where
  \<open>path_bfs succ tgt 0 seen wk = None\<close>
| \<open>path_bfs succ tgt (Suc n) seen [] = None\<close>
| \<open>path_bfs succ tgt (Suc n) seen ((i, p) # wk) =
     (if i = tgt then Some (rev p)
      else (let succs = fold (\<lambda>(X, j) acc.
              if j \<in> set seen \<or> j \<in> set (map fst wk) \<or> j \<in> set (map fst acc) then acc
              else acc @ [(j, X # p)]) (succ i) []
        in path_bfs succ tgt n (i # seen) (wk @ succs)))\<close>

definition prod_no :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow> nat\<close> where
  \<open>prod_no G pr = (case filter (\<lambda>(i, q). q = pr) (zip [0..<length (iprods G)] (iprods G)) of
     [] \<Rightarrow> length (iprods G) | (i, _) # _ \<Rightarrow> i)\<close>

subsection \<open>The conflicting actions of a reported state\<close>

datatype 't xact = XShift 't wrel | XReduce nat wrel

text \<open>The pairs of \<^const>\<open>ipairs_at\<close> that fire under
  \<^const>\<open>ifire\<close>, plus the end-of-input reduce/reduce pairs of
  \<^const>\<open>rr_none_at\<close>, with the actions kept: each carries the relation of
  the lookahead's column to the indentation of the acting item's left-hand
  side.\<close>

definition rpairs_explained :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) witem list list \<Rightarrow> ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow>
    ('t option \<times> 't xact \<times> 't xact) list\<close> where
  \<open>rpairs_explained G Shn sp wrs L i =
     (let reds = ireds_gen Shn (wrs ! i) L i;
         shifts = ishifts (wrs ! i);
         fires = (\<lambda>c\<^sub>1 c\<^sub>2. ifire Shn wrs (pgtab G sp) (anchored_nts G) (ifuel wrs)
             [] [(i, c\<^sub>1, c\<^sub>2)]);
         rr = concat (map (\<lambda>(t, (pr, m, \<tau>)).
                List.map_filter (\<lambda>(t', (pr', m', \<tau>')).
                  if prod_no G pr < prod_no G pr' \<and> t' = t \<and>
                     (t = None \<or> fires (pr, m, \<tau>) (pr', m', \<tau>'))
                  then Some (t, XReduce (prod_no G pr) \<tau>, XReduce (prod_no G pr') \<tau>')
                  else None) reds) reds);
         sr = concat (map (\<lambda>(t, (pr, m, \<tau>)). case t of None \<Rightarrow> [] | Some a \<Rightarrow>
                List.map_filter (\<lambda>(a', (pr', m', \<tau>')).
                  if a' = a \<and> fires (pr, m, \<tau>) (pr', m', \<tau>')
                  then Some (t, XReduce (prod_no G pr) \<tau>, XShift a \<tau>') else None) shifts) reds)
     in remdups (rr @ sr))\<close>

text \<open>The search is budgeted: at most three columns, at most 48 annotated
  words per conflict over all its lookaheads (a witness of a real ambiguity
  is typically among the first few; the budget bounds the cost of the
  over-approximating case).

  All column assignments of a token sequence, and the first of a list
  of annotated words on which the driver reaches an admissible configuration
  (for the report: one in the reported state) with two live
  candidates: the word, how many tokens remain unread there, and the
  candidates (\<^const>\<open>None\<close> for a shift, the production index for a
  reduce).  The exploration runs over precomputed tables and a frontier,
  never recomputing the automaton per configuration.\<close>

fun layouts :: \<open>'t list \<Rightarrow> nat list \<Rightarrow> ('t \<times> nat) list list\<close> where
  \<open>layouts [] cs = [[]]\<close>
| \<open>layouts (a # as) cs = concat (map (\<lambda>w. map (\<lambda>c. (a, c) # w) cs) (layouts as cs))\<close>

definition ncols :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>ncols k = (case filter (\<lambda>c. c ^ k \<le> 32) [2..<4] of [] \<Rightarrow> 2 | cs \<Rightarrow> last cs)\<close>

definition wit_cands :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow>
    ('n, 't) gconfig \<times> ('n, 't) xitem list list \<times> nat list \<Rightarrow>
    (('n, 't) dact \<times> ('n, 't) gconfig \<times> ('n, 't) xitem list list \<times> nat list) list\<close> where
  \<open>wit_cands G sts gt redtab = (\<lambda>(gc, cstk, istk).
     let i = (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j);
         cells = (if i < length redtab then redtab ! i else []);
         CL = (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c)
     in List.map_filter (\<lambda>a. case mstep_cached G cstk gc a of
            Some gc' \<Rightarrow>
              (if dlive gc'
               then Some (a, gc', (case a of
                      DShift \<Rightarrow> (xclosure_auto G (hd (fst gc')) # cstk,
                                dnext gt sts i (Tm (fst (hd (snd gc)))) # istk)
                    | DReduce pr \<Rightarrow> (xclosure_auto G (hd (fst gc')) # drop (length (snd pr)) cstk,
                                dnext gt sts (istk ! length (snd pr)) (Nt (fst pr))
                                  # drop (length (snd pr)) istk)))
               else None)
          | None \<Rightarrow> None)
          (dcands G i cells CL gc))\<close>

fun wit_search :: \<open>('st \<Rightarrow> (('n, 't) dact \<times> 'st) list) \<Rightarrow> ('st \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow>
    'st list \<Rightarrow> ('st \<times> ('n, 't) dact list) option\<close> where
  \<open>wit_search cands ok 0 fr = None\<close>
| \<open>wit_search cands ok (Suc n) fr =
     (if fr = [] then None
      else (let cs = map (\<lambda>st. (st, cands st)) fr in
        case filter (\<lambda>(st, c). ok st \<and> 1 < length c) cs of
          (st, c) # _ \<Rightarrow> Some (st, map fst c)
        | [] \<Rightarrow> wit_search cands ok n (remdups (concat (map (\<lambda>(st, c). map snd c) cs)))))\<close>

fun first_witness :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list \<times> ('n, 't) xitem list \<times> nat \<Rightarrow>
    (('n, 't) gconfig \<times> ('n, 't) xitem list list \<times> nat list \<Rightarrow>
      (('n, 't) dact \<times> ('n, 't) gconfig \<times> ('n, 't) xitem list list \<times> nat list) list) \<Rightarrow>
    (('n, 't) gconfig \<times> ('n, 't) xitem list list \<times> nat list \<Rightarrow> bool) \<Rightarrow>
    nat \<Rightarrow> ('t \<times> nat) list list \<Rightarrow> (('t \<times> nat) list \<times> nat \<times> nat option list) option\<close> where
  \<open>first_witness G init cands ok n [] = None\<close>
| \<open>first_witness G init cands ok n (w # ws) =
     (case init of (xi, xc, i\<^sub>0) \<Rightarrow>
      (case wit_search cands ok n [(([xi], w), [xc], [i\<^sub>0])] of
        None \<Rightarrow> first_witness G init cands ok n ws
      | Some ((gc, _, _), acts) \<Rightarrow> Some (w, length (snd gc),
          map (\<lambda>a. case a of DShift \<Rightarrow> None | DReduce pr \<Rightarrow> Some (prod_no G pr)) acts)))\<close>

subsection \<open>The explanations of a reported state\<close>

text \<open>Three levels, each over the one before: the symbol path from the start
  state to a reported state (all the report shows under
  \<^theory_text>\<open>[[grammar_explain = false]]\<close>); the items of the state and the
  conflicting action pairs; and the sample input (nonterminals expanded to
  shortest terminal words) with a layout witness for the sample extended by
  each conflict lookahead.  The command searches witnesses in the first
  \<^theory_text>\<open>[[grammar_explain_states]]\<close> reported states only and stops at the second
  level for the rest; the functions themselves are total on any state list.\<close>

definition explain_paths :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat list \<Rightarrow>
    (nat \<times> ('n, 't) sym list option) list\<close> where
  \<open>explain_paths G Shn is = (let sp = pr0_states G Shn; gp = pgtab G sp
     in map (\<lambda>i. (i, path_bfs (\<lambda>j. if j < length gp then gp ! j else []) i
          (Suc (length sp)) [] [(p0start G Shn, [])])) is)\<close>

definition explain_rp_brief :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat list \<Rightarrow>
    (nat \<times> (nat \<times> nat) list \<times> ('n, 't) sym list option \<times>
     ('t option \<times> 't xact \<times> 't xact) list) list\<close> where
  \<open>explain_rp_brief G Shn is = (let sp = pr0_states G Shn; L = la_fix G Shn;
       wrs = map (wreach G) sp
     in map (\<lambda>(i, path). let
          items = (if i < length sp then map (\<lambda>(pr, m). (prod_no G pr, m)) (sp ! i) else []);
          prs = (if i < length sp then rpairs_explained G Shn sp wrs L i else [])
        in (i, items, path, prs)) (explain_paths G Shn is))\<close>

definition explain_rp :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat list \<Rightarrow>
    (nat \<times> (nat \<times> nat) list \<times> ('n, 't) sym list option \<times> 't list option \<times>
     ('t option \<times> 't xact \<times> 't xact) list \<times>
     (('t \<times> nat) list \<times> nat \<times> nat option list) option) list\<close> where
  \<open>explain_rp G Shn is = (let
       sp = pr0_states G Shn; gp = pgtab G sp; mw = min_words G;
       cands = wit_cands G sp gp (red_buckets G Shn (length sp));
       xi = xinit G Shn; init = (xi, xclosure_auto G xi, p0start G Shn)
     in map (\<lambda>(i, items, path, prs). let
          sample = (case path of None \<Rightarrow> None | Some p \<Rightarrow> syms_word mw p);
          wit = (case sample of None \<Rightarrow> None | Some w \<Rightarrow>
                  (let ws = map (\<lambda>t. case t of None \<Rightarrow> w | Some a \<Rightarrow> w @ [a])
                              (remdups (map fst prs));
                       cs = [0..<ncols (length w + 1)]
                   in first_witness G init cands
                        (\<lambda>(_, _, istk). istk \<noteq> [] \<and> hd istk = i) (4 * (length w + 2) + 8)
                        (take 48 (concat (map (\<lambda>u. layouts u cs) ws)))))
        in (i, items, path, sample, prs, wit)) (explain_rp_brief G Shn is))\<close>

text \<open>For \<^const>\<open>acc_conflicts\<close>: the state, the productions reduced at end
  of input next to the completed start item, and the path to it in the
  automaton.\<close>

definition explain_acc :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat list \<Rightarrow>
    (nat \<times> nat list \<times> ('n, 't) sym list option \<times> 't list option) list\<close> where
  \<open>explain_acc G Shn is = (let
       sp = pr0_states G Shn; gp = pgtab G sp; L = la_fix G Shn; mw = min_words G
     in map (\<lambda>i. let
          prs = remdups (List.map_filter (\<lambda>(i', (pr, m), t, \<tau>).
                  if i' = i \<and> m = length (snd pr) \<and> t = None \<and> pr \<noteq> start_prod G Shn
                  then Some (prod_no G pr) else None) L);
          path = path_bfs (\<lambda>j. if j < length gp then gp ! j else []) i
                   (Suc (length sp)) [] [(p0start G Shn, [])];
          sample = (case path of None \<Rightarrow> None | Some p \<Rightarrow> syms_word mw p)
        in (i, prs, path, sample)) is)\<close>


section \<open>The checks of the \<^theory_text>\<open>parser\<close> command\<close>

text \<open>The command evaluates these five values and nothing else: the two conflict
  reports, the symbol paths of the reported states (the report's cheapest level,
  \<^const>\<open>explain_paths\<close>, over the automaton the checks have built), whether the
  grammar has no layout annotations (\<^const>\<open>ii\<close>, the simple driver's condition)
  and whether every reduce cell with a token is unconstrained in width
  (\<^const>\<open>wany_ok\<close>). The \<open>let\<close> shares the automaton, its goto table and the
  saturated cells between them. The tables themselves stay
  symbolic: the parser's table constants are defined by their terms
  (\<^text>\<open>lr_build_parse\<close>), so the generated code computes each once when it loads, and
  no table is rebuilt as a term, which cost more than computing it.\<close>

definition lr_checks :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> 't list \<Rightarrow> nat list \<times> nat list \<times>
    bool \<times> bool \<times> (nat \<times> ('n, 't) sym list option) list \<times> nat list\<close> where
  \<open>lr_checks G Shn ctrs =
     (let sp = pr0_states G Shn; gp = pgtab G sp; L = la_fix_gen G Shn gp sp;
          ants = anchored_nts G; wrs = map (wreach G) sp; fuel = ifuel wrs;
          p0 = p0start G Shn; s0 = start_prod G Shn;
          confs = filter (rlalr_conflict_at_gen Shn wrs gp ants fuel L) [0..<length sp]
      in (confs,
          filter (\<lambda>i. (s0, Suc 0) \<in> set (sp ! i) \<and>
                    list_ex (\<lambda>(i', (pr, m), t, \<tau>). i' = i \<and> m = length (snd pr) \<and>
                              t = None \<and> pr \<noteq> s0) L)
            [0..<length sp],
          ii G, wany_ok (cell_buckets L (length sp)),
          map (\<lambda>i. (i, path_bfs (\<lambda>j. if j < length gp then gp ! j else []) i
               (Suc (length sp)) [] [(p0, [])])) confs,
          map (ntidx (vtoks G (cell_buckets L (length sp)))) ctrs))\<close>

theorem lr_checks_eq:
  \<open>lr_checks G Shn ctrs =
     (rlalr_conflicts G Shn, acc_conflicts G Shn, ii G,
      wany_ok (red_buckets G Shn (length (pr0_states G Shn))),
      explain_paths G Shn (rlalr_conflicts G Shn), vnums G Shn ctrs)\<close>
  by (simp add: lr_checks_def vnums_def explain_paths_def red_buckets_def la_fix_def
        rlalr_conflicts_code acc_conflicts_code Let_def)


text \<open>The simple driver's table construction needs one more value: the numbers of
  the token constructors (\<^const>\<open>pnum\<close>). They are computed from the tables the
  parser's constants are defined by, in the same shape, so the backend turns the
  evaluated equation into one over its constants by rewriting with their definitions.\<close>

definition lr_simple_checks :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> 't list \<Rightarrow> nat list\<close> where
  \<open>lr_simple_checks G Shn ctrs =
     (let sts = pr0_states G Shn; gt = pgtab G sts; redtab = red_buckets G Shn (length sts);
          pc = pcomps G sts; pf = pfins Shn sts;
          K = ktabs_of (jtabs_of (mk_ltabs gt sts redtab pc pf))
      in map (pnum (ptabs_of K)) ctrs)\<close>

text \<open>Under \<^text>\<open>parser_literal_tables\<close>, the tables of the state-indexed driver
  are evaluated as well, in one evaluation.\<close>

definition lr_vec_tables :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow>
    ('n, 't) stab \<times> ('n, 't) vtab \<times> ('n, 't) vktab \<times> ('n, 't) sitem list \<times> ('n, 't) sitem list\<close> where
  \<open>lr_vec_tables G Shn =
     (let sts = pr0_states G Shn; gt = pgtab G sts; rt = red_buckets G Shn (length sts);
          T = mk_stab G Shn gt sts rt; V = mk_vtab G Shn T sts gt rt; kin = sinit T
      in (T, V, mk_vktab V, kin, sclosure T kin))\<close>

lemma lr_vec_tables_eq:
  \<open>lr_vec_tables G Shn =
     (mk_stab G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn)
        (red_buckets G Shn (length (pr0_states G Shn))),
      mk_vtab G Shn
        (mk_stab G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn)
           (red_buckets G Shn (length (pr0_states G Shn))))
        (pr0_states G Shn) (pgtab G (pr0_states G Shn))
        (red_buckets G Shn (length (pr0_states G Shn))),
      mk_vktab (mk_vtab G Shn
        (mk_stab G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn)
           (red_buckets G Shn (length (pr0_states G Shn))))
        (pr0_states G Shn) (pgtab G (pr0_states G Shn))
        (red_buckets G Shn (length (pr0_states G Shn)))),
      sinit (mk_stab G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn)
        (red_buckets G Shn (length (pr0_states G Shn)))),
      sclosure (mk_stab G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn)
          (red_buckets G Shn (length (pr0_states G Shn))))
        (sinit (mk_stab G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn)
          (red_buckets G Shn (length (pr0_states G Shn))))))\<close>
  by (simp add: lr_vec_tables_def Let_def)

section \<open>Coverage of the errors of a parser\<close>

text \<open>What \<^file>\<open>lr_reach.ML\<close> reads, as numbers, so that the tables are evaluated once:
  the automaton, the pairs of a state and a terminal whose action depends on the columns, and
  the driver as a function on words of terminals with their columns. Nothing here is
  proved, and nothing depends on it but warnings and the skeleton of an \<open>errors\<close> block
  \<^cite>\<open>\<open>Sect.~3\<close> in "pottier2016-lr1-reachability"\<close>.

  The states hold kernels, so a shift counts as decided by the columns if its terminal
  has a relation anywhere in the grammar. A reduction does if its cell has a relation,
  or if the left-hand side occurs with one, as the goto then narrows the anchors.\<close>

definition lr_rel_syms :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) sym list\<close> where
  \<open>lr_rel_syms G = remdups (concat (map (\<lambda>(A, rhs).
     map fst (filter (\<lambda>(X, r). r \<noteq> Any) rhs)) (iprods G)))\<close>

definition lr_dep :: \<open>('n, 't) is_cfg \<Rightarrow> 't list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) lacell list list \<Rightarrow> nat list\<close> where
  \<open>lr_dep G ts gt rt = (let ss = lr_rel_syms G in
     concat (map (\<lambda>(i, row). concat (map (\<lambda>(X, _). (case X of
         Tm a \<Rightarrow> if X \<in> set ss then [i, ntidx ts a] else []
       | Nt _ \<Rightarrow> [])) row)) (zip [0..<length gt] gt)) @
     concat (map (\<lambda>r. concat (map (\<lambda>(i, (pr, m), t, \<tau>).
       if \<tau> \<noteq> WAny \<or> Nt (fst pr) \<in> set ss
       then [i, case t of None \<Rightarrow> length ts | Some a \<Rightarrow> ntidx ts a] else []) r)) rt))\<close>

text \<open>\<open>on_error_reduce\<close> \<^cite>\<open>\<open>Sect.~4\<close> in "pottier2016-lr1-reachability"\<close>:
  in the second run on a rejected word a state reduces a production of a named
  nonterminal on every terminal it has no action on. The production is the lowest one the
  state can reduce. The parser and its tables stay as they are.\<close>

definition oer_prods :: \<open>'n list \<Rightarrow> ('n, 't) is_cfg \<Rightarrow> ('n, 't) lacell list \<Rightarrow>
    ('n \<times> ('n, 't) rhs) list\<close> where
  \<open>oer_prods As G row = filter (\<lambda>pr. fst pr \<in> set As \<and>
     list_ex (\<lambda>(_, (pr', _), _, _). pr' = pr) row) (iprods G)\<close>

definition oer_row :: \<open>'n list \<Rightarrow> ('n, 't) is_cfg \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
    (('n, 't) sym \<times> nat) list \<Rightarrow> ('n, 't) lacell list \<Rightarrow> ('n, 't) lacell list\<close> where
  \<open>oer_row As G ts i fin gr row = (case oer_prods As G row of
       [] \<Rightarrow> row
     | pr # _ \<Rightarrow>
         row @ map (\<lambda>z. (i, (pr, length (snd pr)), z, WAny))
           (filter (\<lambda>z. \<not> list_ex (\<lambda>(_, _, t, _). t = z) row \<and>
              (case z of None \<Rightarrow> \<not> fin | Some a \<Rightarrow> map_of gr (Tm a) = None))
            (None # map Some ts)))\<close>

definition oer_cells :: \<open>'n list \<Rightarrow> ('n, 't) is_cfg \<Rightarrow> 't list \<Rightarrow> bool list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> ('n, 't) lacell list list\<close> where
  \<open>oer_cells As G ts pf gt rt =
     map (\<lambda>(i, fin, gr, row). oer_row As G ts i fin gr row) (zip [0..<length rt] (zip pf (zip gt rt)))\<close>

definition oer_diag :: \<open>('w \<Rightarrow> 'e + 'x) \<Rightarrow> ('w \<Rightarrow> 'e + 'x) \<Rightarrow> 'w \<Rightarrow> 'e + 'x\<close> where
  \<open>oer_diag f g w = (case f w of
     Inr x \<Rightarrow> Inr x
   | Inl e \<Rightarrow> (case g w of Inl e' \<Rightarrow> Inl e' | Inr _ \<Rightarrow> Inl e))\<close>

lemma oer_diag_Inr_iff: \<open>oer_diag f g w = Inr x \<longleftrightarrow> f w = Inr x\<close>
  by (simp add: oer_diag_def split: sum.split)

text \<open>In the recovery the plan stays that of the parser's tables, and the report is the
  one of \<open>oer_diag\<close>, with the repair of the plan.\<close>

definition oer_stop :: \<open>(nat \<Rightarrow> 'w \<Rightarrow> (('n, 't, 'ch, 'm) perr \<times> 'p) option) \<Rightarrow>
    ('w \<Rightarrow> ('n, 't, 'ch, 'm) perr + 'x) \<Rightarrow> nat \<Rightarrow> 'w \<Rightarrow> (('n, 't, 'ch, 'm) perr \<times> 'p) option\<close> where
  \<open>oer_stop stop g b w = map_option (\<lambda>(e, pl).
     (case g w of Inl e' \<Rightarrow> e'\<lparr>pe_repair := pe_repair e\<rparr> | Inr _ \<Rightarrow> e, pl)) (stop b w)\<close>

text \<open>For the pruning of the candidates that depend on columns (\<^file>\<open>lr_reach.ML\<close>), the
  relations of the productions, the kernels, and the relation of each reduce cell, as numbers.
  A kernel item of no production of the grammar (the start item) gets the number of
  productions.\<close>

definition lr_irel_code :: \<open>irel \<Rightarrow> nat\<close> where
  \<open>lr_irel_code r = (case r of Eq \<Rightarrow> 0 | Gt \<Rightarrow> 1 | Ge \<Rightarrow> 2 | Any \<Rightarrow> 3)\<close>

definition lr_wrel_code :: \<open>wrel \<Rightarrow> nat\<close> where
  \<open>lr_wrel_code \<tau> = (case \<tau> of WEq \<Rightarrow> 0 | WGe \<Rightarrow> 1 | WGt \<Rightarrow> 2 | WLe \<Rightarrow> 3 | WLt \<Rightarrow> 4 | WAny \<Rightarrow> 5)\<close>

definition lr_view :: \<open>'n list \<Rightarrow> ('n, 't) is_cfg \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> 't list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow>
    integer list list\<close> where
  \<open>lr_view As G pf i0 ts sts gt rt = (let
     nts = remdups (map fst (iprods G)); nt = length ts;
     prs = zip (iprods G) [0..<length (iprods G)];
     pnum = (\<lambda>pr. case map_of prs pr of None \<Rightarrow> length (iprods G) | Some p \<Rightarrow> p);
     sc = (\<lambda>X. case X of Tm a \<Rightarrow> ntidx ts a | Nt A \<Rightarrow> nt + 1 + ntidx nts A)
   in map (map integer_of_nat)
     [[length sts, nt, length nts, i0],
      concat (map (\<lambda>(i, row). concat (map (\<lambda>(X, j). [i, sc X, j]) row)) (zip [0..<length gt] gt)),
      concat (map (\<lambda>(A, rhs). ntidx nts A # length rhs # map (sc \<circ> fst) rhs) (iprods G)),
      concat (map (\<lambda>r. concat (map (\<lambda>(i, (pr, m), t, \<tau>). case map_of prs pr of None \<Rightarrow> []
            | Some p \<Rightarrow> [i, p, case t of None \<Rightarrow> nt | Some a \<Rightarrow> ntidx ts a]) r)) rt),
      map fst (filter snd (zip [0..<length sts] pf)),
      lr_dep G ts gt rt,
      concat (map (\<lambda>(i, r). if Suc 0 < length (oer_prods As G r) then [i] else [])
        (zip [0..<length rt] rt)),
      concat (map (\<lambda>(A, rhs). length rhs # map (lr_irel_code \<circ> snd) rhs) (iprods G)),
      concat (map (\<lambda>(i, k). i # length k # concat (map (\<lambda>(pr, m). [pnum pr, m]) k))
        (zip [0..<length sts] sts)),
      concat (map (\<lambda>r. concat (map (\<lambda>(i, (pr, m), t, \<tau>). [i, pnum pr, m,
          case t of None \<Rightarrow> nt | Some a \<Rightarrow> ntidx ts a, lr_wrel_code \<tau>]) r)) rt)])\<close>

fun reach_pairs :: \<open>integer list \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>reach_pairs (a # b # r) = (nat_of_integer a, nat_of_integer b) # reach_pairs r\<close>
| \<open>reach_pairs _ = []\<close>

text \<open>A rejected word as numbers, \<open>[]\<close> for an accepted one: the end of the input is
  \<^term>\<open>length ts\<close>, and a terminal of no production the number after it.\<close>

definition reach_enc :: \<open>'t list \<Rightarrow> (nat \<times> 't option \<times> nat \<times> nat \<times> nat) option \<Rightarrow> integer list\<close> where
  \<open>reach_enc ts r = (case r of
     None \<Rightarrow> []
   | Some (st, tk, sh, idx, depth) \<Rightarrow> map integer_of_nat
       [st, case tk of None \<Rightarrow> length ts
          | Some a \<Rightarrow> if a \<in> set ts then ntidx ts a else Suc (length ts),
        sh, idx, depth])\<close>

definition reach_fn :: \<open>(('t, 'ch, 'm) token_scheme list \<Rightarrow> ('n, 't, 'ch, 'm) perr + 'x) \<Rightarrow>
    ('t \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> ('t, 'ch, 'm) token_scheme) \<Rightarrow> ('t \<times> string) list \<Rightarrow>
    integer list \<Rightarrow> integer list\<close> where
  \<open>reach_fn probe mk tss is =
     reach_enc (map fst tss) (diag_probe (probe (map (\<lambda>(t, c).
       (case tss ! t of (a, s) \<Rightarrow> mk a s c)) (reach_pairs is))))\<close>

text \<open>The checks with the errors of the words of an \<open>errors\<close> block, in one evaluation:
  the words run on the state-indexed driver over the automaton of the checks, as the
  parser's \<open>p_probe\<close> runs them over its constants, so that the tables are built once.
  The errors are not proved, only the checks: they are the first component. A grammar
  for the simple driver gets no errors here.\<close>

definition lr_checks_keys :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> 't list \<Rightarrow> 't list \<Rightarrow>
    ('m, 'ch, 't) tword list \<Rightarrow> (nat list \<times> nat list \<times> bool \<times> bool \<times>
      (nat \<times> ('n, 't) sym list option) list \<times> nat list) \<times> integer list list\<close> where
  \<open>lr_checks_keys G Shn ctrs ts ws =
     (let sp = pr0_states G Shn; gp = pgtab G sp; L = la_fix_gen G Shn gp sp;
          ants = anchored_nts G; wrs = map (wreach G) sp; fuel = ifuel wrs;
          p0 = p0start G Shn; s0 = start_prod G Shn;
          confs = filter (rlalr_conflict_at_gen Shn wrs gp ants fuel L) [0..<length sp];
          rt = cell_buckets L (length sp); i = ii G; wa = wany_ok rt
      in ((confs,
           filter (\<lambda>i. (s0, Suc 0) \<in> set (sp ! i) \<and>
                     list_ex (\<lambda>(i', (pr, m), t, \<tau>). i' = i \<and> m = length (snd pr) \<and>
                               t = None \<and> pr \<noteq> s0) L)
             [0..<length sp],
           i, wa,
           map (\<lambda>i. (i, path_bfs (\<lambda>j. if j < length gp then gp ! j else []) i
                (Suc (length sp)) [] [(p0, [])])) confs,
           map (ntidx (vtoks G rt)) ctrs),
          if i \<and> confs = [] \<and> wa then []
          else
            (let T = mk_stab G Shn gp sp rt; V = mk_vtab G Shn T sp gp rt; kin = sinit T;
                 i\<^sub>0 = st_find sp (lr0_start G Shn)
             in map (\<lambda>w. reach_enc ts (diag_probe
                  (vdiag V T kin (sclosure T kin) i\<^sub>0 [] (\<lambda>_. Some ()) w))) ws)))\<close>

lemma lr_checks_keys_fst: \<open>fst (lr_checks_keys G Shn ctrs ts ws) = lr_checks G Shn ctrs\<close>
  by (simp add: lr_checks_keys_def lr_checks_def Let_def)

section \<open>The LR backend of the \<^theory_text>\<open>parser\<close> command\<close>

ML_file \<open>lr_reach.ML\<close>
ML_file \<open>lr_util.ML\<close>
ML_file \<open>lr_diag.ML\<close>
ML_file \<open>lr_build.ML\<close>
ML_file \<open>lr.ML\<close>

end
