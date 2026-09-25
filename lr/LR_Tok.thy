theory LR_Tok
  imports LR_Trie
begin

section \<open>Numbering the tokens once\<close>

text \<open>The trie step numbers the lookahead token at every step, by a search
  in the list of tokens of the tables. Here the input word is numbered once,
  as a list of pairs of a token and its number, and the driver reads the
  number off the input.\<close>

definition xtree :: \<open>('w \<Rightarrow> ('t, 'ch, 'm) token_scheme) \<Rightarrow> ('n, 't) dact \<Rightarrow> 'w list \<Rightarrow>
    ('m, 'ch, 'n, 't) ast list \<Rightarrow> ('m, 'ch, 'n, 't) ast list\<close> where
  \<open>xtree dec act v tstk = (case act of
      DShift \<Rightarrow> Leaf (dec (hd v)) # tstk
    | DReduce pr \<Rightarrow> Node (fst pr) (rev (take_as (snd pr) tstk)) # drop_as (snd pr) tstk)\<close>

partial_function (option) xrun_hist ::
  \<open>((nat \<times> nat) list \<times> 'w list \<Rightarrow> (('n, 't) dact \<times> (nat \<times> nat) list \<times> 'w list) option) \<Rightarrow>
    ((nat \<times> nat) list \<times> 'w list \<Rightarrow> bool) \<Rightarrow> ('w \<Rightarrow> ('t, 'ch, 'm) token_scheme) \<Rightarrow>
    (nat \<times> nat) list list \<Rightarrow> (nat \<times> nat) list \<times> 'w list \<times> ('m, 'ch, 'n, 't) ast list \<Rightarrow>
    ('m, 'ch, 'n, 't) ast option\<close>
  where
  \<open>xrun_hist ctl fin dec seen st = (case st of (stk, v, tstk) \<Rightarrow>
     if fin (stk, v) then sresult tstk
     else if stk \<in> set seen then None
     else Option.bind (ctl (stk, v)) (\<lambda>(act, stk', v').
       xrun_hist ctl fin dec (if act = DShift then [] else stk # seen)
         (stk', v', xtree dec act v tstk)))\<close>

lemmas xrun_hist_simps [code] = xrun_hist.simps

text \<open>\<^const>\<open>xrun_hist\<close> on an encoded input computes \<^const>\<open>srun_hist\<close>.\<close>

locale input_transfer =
  fixes enc :: \<open>('t, 'ch, 'm) token_scheme \<Rightarrow> 'w\<close> and dec :: \<open>'w \<Rightarrow> ('t, 'ch, 'm) token_scheme\<close>
    and ctl1 :: \<open>('m, 'ch, 't) sctl_t \<Rightarrow> (('n, 't) dact \<times> ('m, 'ch, 't) sctl_t) option\<close>
    and fin1 :: \<open>('m, 'ch, 't) sctl_t \<Rightarrow> bool\<close>
    and ctl2 :: \<open>(nat \<times> nat) list \<times> 'w list \<Rightarrow> (('n, 't) dact \<times> (nat \<times> nat) list \<times> 'w list) option\<close>
    and fin2 :: \<open>(nat \<times> nat) list \<times> 'w list \<Rightarrow> bool\<close>
  assumes dec: \<open>\<And>x. dec (enc x) = x\<close>
    and ctl: \<open>\<And>stk v. ctl2 (stk, map enc v) =
      map_option (\<lambda>(a, stk', v'). (a, stk', map enc v')) (ctl1 (stk, v))\<close>
    and fin: \<open>\<And>stk v. fin2 (stk, map enc v) = fin1 (stk, v)\<close>
    and shift: \<open>\<And>stk v r. ctl1 (stk, v) = Some (DShift, r) \<Longrightarrow> v \<noteq> []\<close>
begin

lemma xtree_stree:
  \<open>ctl1 (stk, v) = Some (a, r) \<Longrightarrow> xtree dec a (map enc v) tstk = stree a v tstk\<close>
  using shift[of stk v] dec
  by (cases a) (auto simp: xtree_def stree_code hd_map)

lemma s_imp_x:
  assumes h: \<open>srun_hist ctl1 fin1 seen st = Some t\<close>
  shows \<open>xrun_hist ctl2 fin2 dec seen (fst st, map enc (fst (snd st)), snd (snd st)) = Some t\<close>
proof -
  have \<open>ctl1 = ctl1 \<longrightarrow> fin1 = fin1 \<longrightarrow>
      xrun_hist ctl2 fin2 dec seen (fst st, map enc (fst (snd st)), snd (snd st)) = Some t\<close>
  proof (rule srun_hist.raw_induct[OF _ h, where P = \<open>\<lambda>ctl fin seen st t. ctl = ctl1 \<longrightarrow> fin = fin1 \<longrightarrow>
      xrun_hist ctl2 fin2 dec seen (fst st, map enc (fst (snd st)), snd (snd st)) = Some t\<close>], goal_cases)
    case (1 f ctl fin seen st t)
    obtain stk v tstk where st: \<open>st = (stk, v, tstk)\<close> by (cases st)
    show ?case
    proof (intro impI)
      assume c: \<open>ctl = ctl1\<close> and fi: \<open>fin = fin1\<close>
      show \<open>xrun_hist ctl2 fin2 dec seen (fst st, map enc (fst (snd st)), snd (snd st)) = Some t\<close>
      proof (cases \<open>fin1 (stk, v)\<close>)
        case True
        with "1"(2) show ?thesis unfolding st c fi by (subst xrun_hist.simps) (simp add: fin)
      next
        case False
        from False "1"(2) have nk: \<open>stk \<notin> set seen\<close> unfolding st c fi by (auto split: if_splits)
        from False "1"(2) obtain a stk' v' where
            sc: \<open>ctl1 (stk, v) = Some (a, stk', v')\<close>
          and rec: \<open>f ctl fin (if a = DShift then [] else stk # seen) (stk', v', stree a v tstk) = Some t\<close>
          unfolding st c fi by (auto simp: bind_eq_Some_conv split: if_splits)
        from "1"(1)[OF rec] c fi
        have \<open>xrun_hist ctl2 fin2 dec (if a = DShift then [] else stk # seen)
            (stk', map enc v', stree a v tstk) = Some t\<close> by simp
        then show ?thesis unfolding st using False nk sc xtree_stree[OF sc]
          by (subst xrun_hist.simps) (simp add: fin ctl)
      qed
    qed
  qed
  then show ?thesis by blast
qed

lemma x_imp_s:
  assumes h: \<open>xrun_hist ctl2 fin2 dec seen st2 = Some t\<close>
  shows \<open>st2 = (stk, map enc v, tstk) \<Longrightarrow> srun_hist ctl1 fin1 seen (stk, v, tstk) = Some t\<close>
proof -
  have \<open>ctl2 = ctl2 \<longrightarrow> fin2 = fin2 \<longrightarrow> dec = dec \<longrightarrow> (\<forall>stk v tstk.
      st2 = (stk, map enc v, tstk) \<longrightarrow> srun_hist ctl1 fin1 seen (stk, v, tstk) = Some t)\<close>
  proof (rule xrun_hist.raw_induct[OF _ h, where P = \<open>\<lambda>ctl fin dc seen st2 t. ctl = ctl2 \<longrightarrow> fin = fin2 \<longrightarrow>
      dc = dec \<longrightarrow> (\<forall>stk v tstk. st2 = (stk, map enc v, tstk) \<longrightarrow>
        srun_hist ctl1 fin1 seen (stk, v, tstk) = Some t)\<close>], goal_cases)
    case (1 f ctl fin dc seen st2 t)
    show ?case
    proof (intro impI allI)
      fix stk v tstk
      assume c: \<open>ctl = ctl2\<close> and fi: \<open>fin = fin2\<close> and d: \<open>dc = dec\<close>
        and st: \<open>st2 = (stk, map enc v, tstk)\<close>
      show \<open>srun_hist ctl1 fin1 seen (stk, v, tstk) = Some t\<close>
      proof (cases \<open>fin1 (stk, v)\<close>)
        case True
        with "1"(2) show ?thesis unfolding st c fi by (subst srun_hist.simps) (simp add: fin)
      next
        case False
        from False "1"(2) have nk: \<open>stk \<notin> set seen\<close>
          unfolding st c fi by (auto simp: fin split: if_splits)
        from False "1"(2) obtain a stk' v2 where
            sc: \<open>ctl2 (stk, map enc v) = Some (a, stk', v2)\<close>
          and rec: \<open>f ctl fin dc (if a = DShift then [] else stk # seen)
              (stk', v2, xtree dc a (map enc v) tstk) = Some t\<close>
          unfolding st c fi by (auto simp: bind_eq_Some_conv fin split: if_splits)
        from sc obtain v' where sc1: \<open>ctl1 (stk, v) = Some (a, stk', v')\<close> and v2: \<open>v2 = map enc v'\<close>
          unfolding ctl by (auto split: prod.splits)
        have \<open>srun_hist ctl1 fin1 (if a = DShift then [] else stk # seen) (stk', v', stree a v tstk) = Some t\<close>
          using "1"(1)[OF rec] c fi d v2 xtree_stree[OF sc1] by simp
        then show ?thesis using False nk sc1 by (subst srun_hist.simps) simp
      qed
    qed
  qed
  then show \<open>st2 = (stk, map enc v, tstk) \<Longrightarrow> srun_hist ctl1 fin1 seen (stk, v, tstk) = Some t\<close> by blast
qed

theorem xrun_hist_eq:
  \<open>xrun_hist ctl2 fin2 dec seen (stk, map enc v, tstk) = srun_hist ctl1 fin1 seen (stk, v, tstk)\<close>
proof (cases \<open>srun_hist ctl1 fin1 seen (stk, v, tstk)\<close>)
  case None
  show ?thesis
  proof (cases \<open>xrun_hist ctl2 fin2 dec seen (stk, map enc v, tstk)\<close>)
    case (Some t)
    from x_imp_s[OF Some refl] None show ?thesis by simp
  qed (simp add: None)
next
  case (Some t)
  from s_imp_x[OF Some] Some show ?thesis by simp
qed

end

subsection \<open>The trie step on numbered input\<close>

definition jenc :: \<open>('n, 't) jtabs \<Rightarrow> ('t, 'ch, 'm) token_scheme \<Rightarrow> ('t, 'ch, 'm) token_scheme \<times> nat\<close> where
  \<open>jenc J x = (x, jla J [x])\<close>

definition jctl2 :: \<open>('n, 't) jtabs \<Rightarrow> (nat \<times> nat) list \<times> (('t, 'ch, 'm) token_scheme \<times> nat) list \<Rightarrow>
    (('n, 't) dact \<times> (nat \<times> nat) list \<times> (('t, 'ch, 'm) token_scheme \<times> nat) list) option\<close> where
  \<open>jctl2 J c = (case c of (stk, v) \<Rightarrow>
     (case stk of [] \<Rightarrow> None | (i, p) # _ \<Rightarrow>
       let l = (case v of [] \<Rightarrow> 0 | (_, l) # _ \<Rightarrow> l);
           lics = jget (jt_lic J) i l;
           comps = (case tlookup (jt_pc J) p of None \<Rightarrow> [] | Some cs \<Rightarrow> cs);
           cands = (case v of [] \<Rightarrow> [] | _ \<Rightarrow> [IShift]) @ map IReduce (filter (jlicd lics) comps)
       in (case spick (jtarget J stk l) cands of
            None \<Rightarrow> None
          | Some (IShift, q) \<Rightarrow> Some (DShift, (jgo (jt_cgT J) (jt_ns J) i l, q) # stk, tl v)
          | Some (IReduce j, q) \<Rightarrow> (case tlookup (jt_prs J) j of None \<Rightarrow> None | Some (pr, A) \<Rightarrow>
              (case drop_as (snd pr) stk of [] \<Rightarrow> None | (i', _) # _ \<Rightarrow>
                 Some (DReduce pr, (jgo (jt_cgN J) (jt_ns J) i' A, q) # drop_as (snd pr) stk, v))))))\<close>

definition jfinal2 :: \<open>('n, 't) jtabs \<Rightarrow> (nat \<times> nat) list \<times> (('t, 'ch, 'm) token_scheme \<times> nat) list \<Rightarrow> bool\<close> where
  \<open>jfinal2 J c \<longleftrightarrow> (case c of (stk, v) \<Rightarrow> v = [] \<and>
     (case stk of [] \<Rightarrow> False | (i, p) # _ \<Rightarrow> tlookup (jt_pf J) p = Some True))\<close>

lemma jla_enc: \<open>(case map (jenc J) v of [] \<Rightarrow> 0 | (_, l) # _ \<Rightarrow> l) = jla J v\<close>
  unfolding jenc_def jla_def by (cases v) auto

lemma jctl2_eq:
  \<open>jctl2 J (stk, map (jenc J) v) =
    map_option (\<lambda>(a, stk', v'). (a, stk', map (jenc J) v')) (jctl J (stk, v))\<close>
proof -
  have cs: \<open>(case map (jenc J) v of [] \<Rightarrow> [] | _ \<Rightarrow> [IShift]) = (case v of [] \<Rightarrow> [] | _ \<Rightarrow> [IShift])\<close>
    by (cases v) auto
  show ?thesis
    unfolding jctl2_def jctl_def prod.case jla_enc cs
    by (auto simp: Let_def map_tl split: list.splits option.splits prod.splits iact.splits)
qed

lemma jfinal2_eq: \<open>jfinal2 J (stk, map (jenc J) v) = jfinal J (stk, v)\<close>
  unfolding jfinal2_def jfinal_def by simp

lemma jctl_shift: \<open>jctl J (stk, v) = Some (DShift, r) \<Longrightarrow> v \<noteq> []\<close>
  unfolding jctl_def
  by (auto simp: Let_def split: list.splits option.splits prod.splits iact.splits dest!: spick_SomeD)

theorem xrun_jctl2:
  \<open>xrun_hist (jctl2 J) (jfinal2 J) fst seen (stk, map (jenc J) v, tstk) =
    srun_hist (jctl J) (jfinal J) seen (stk, v, tstk)\<close>
proof -
  interpret input_transfer \<open>jenc J\<close> fst \<open>jctl J\<close> \<open>jfinal J\<close> \<open>jctl2 J\<close> \<open>jfinal2 J\<close>
    by (rule input_transfer.intro) (simp add: jenc_def, rule jctl2_eq, rule jfinal2_eq, rule jctl_shift)
  show ?thesis by (rule xrun_hist_eq)
qed

lemma dparse_via_trie_tok_tables:
  assumes static: \<open>sstatic G Shn\<close>
    and st: \<open>lr0_states G Shn = sts\<close> and gt: \<open>la_gtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and ps: \<open>pr0_states G Shn = psts\<close> and pg: \<open>pgtab G psts = pgt\<close>
    and pcs: \<open>pcomps G psts = pc\<close> and pfs: \<open>pfins Shn psts = pf\<close>
    and i0: \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and p0: \<open>st_find psts (lr0_start G Shn) = p\<^sub>0\<close>
    and lt: \<open>mk_ltabs gtab sts redtab pgt psts pc pf = L\<close>
    and jt: \<open>jtabs_of L = J\<close>
  shows \<open>dparse G Shn w = xrun_hist (jctl2 J) (jfinal2 J) fst [] ([(i\<^sub>0, p\<^sub>0)], map (jenc J) w, [])\<close>
  unfolding dparse_via_trie_tables[OF static st gt rt ps pg pcs pfs i0 p0 lt jt] xrun_jctl2 ..

end
