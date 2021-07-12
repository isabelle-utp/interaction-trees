section \<open> Stability and Divergence \<close>

theory ITree_Divergence
  imports Interaction_Trees
begin

subsection \<open> Stability \<close>

text \<open> A process stabilises if it stabilises within a finite number of internal events \<close>

definition "stabilises P = (\<exists> n P'. (Sils n P' = P \<and> stable P'))"

lemma stabilises_Ret [simp]: "stabilises (Ret x)"
  by (force simp add: stabilises_def)

lemma stabilises_Sil [intro, simp]: 
  "stabilises P \<Longrightarrow> stabilises (Sil P)"
  by (metis Sils.simps(2) stabilises_def)

lemma stabilises_Vis [intro, simp]:
  "stabilises (Vis F)"
  by (metis Sils.simps(1) itree.disc(9) itree.distinct_disc(6) stabilises_def)

lemma stabilises_traceI: "\<lbrakk> P \<midarrow>tr\<leadsto> P'; tr \<noteq> [] \<rbrakk> \<Longrightarrow> stabilises P"
  by (metis append_Cons append_Nil list.distinct(1) list.exhaust stabilises_Vis stabilises_def trace_of_Sils trace_to_VisE trace_to_appendE trace_to_singleE)

text \<open> An @{type itree} stabilises to a relation @{term R} if after stabilising and choosing a 
  new event, the continuation is in @{term R}. \<close>

inductive stabilises_to :: "(('e, 's) itree \<Rightarrow> bool) \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" where
ret_stbs [intro]: "stabilises_to R (Ret x)" |
sil_stbs [intro]: "stabilises_to R P \<Longrightarrow> stabilises_to R (Sil P)" |
vis_stbs [intro]: "(\<And> t. t \<in> pran F \<Longrightarrow> R t) \<Longrightarrow> stabilises_to R (Vis F)"

lemma monotonic_stabilises_to: "stabilises_to R P \<Longrightarrow> R \<le> S \<Longrightarrow> stabilises_to S P"
  apply (induct rule: stabilises_to.induct)
  apply (simp_all add: ret_stbs sil_stbs vis_stbs)
  apply fastforce
  done

lemma mono_stabilises_to [mono add]: "R \<le> S \<Longrightarrow> stabilises_to R \<le> stabilises_to S"
  using monotonic_stabilises_to by auto

lemma stabilises_to_stabilises [intro]: "stabilises_to R P \<Longrightarrow> stabilises P"
  by (induct rule: stabilises_to.induct, auto)

lemma stabilises_to_Sils_VisI [intro]: 
  "pran F \<subseteq> Collect R \<Longrightarrow> stabilises_to R (Sils n (Vis F))"
  by (induct n, auto)

lemma stabilises_to_Sils_RetI [intro]: "stabilises_to R (Sils n (Ret x))"
  by (induct n, auto)

lemma stabilises_alt_def: 
  "stabilises_to R P = (\<exists> n P'. Sils n P' = P \<and> ((P' \<in> range Vis \<and> pran (un_Vis P') \<subseteq> Collect R) \<or> P' \<in> range Ret))"
  apply (auto)
   apply (induct rule: stabilises_to.induct)
  apply (auto)
  apply (meson Sils.simps(1) range_eqI)
  apply (metis Sils.simps(2) itree.sel(3) rangeI)
  apply (meson Sils.simps(2) rangeI)
  apply (metis Collect_mem_eq Collect_mono Sils.simps(1) itree.sel(3) rangeI)
  done

lemma stabilises_alt_def': 
  "stabilises_to R P = 
    ((\<exists> n F. Sils n (Vis F) = P \<and> pran F \<subseteq> Collect R) \<or> (\<exists> n x. Sils n (Ret x) = P))"
  by (auto simp add: stabilises_alt_def, metis itree.sel(3) rangeI, blast)
  
lemma stabilises_to_Sils_Vis [simp]: "stabilises_to R (Sils n (Vis F)) = (pran F \<subseteq> Collect R)"
  by (auto, auto simp add: Sils_Vis_iff stabilises_alt_def image_subset_iff)

subsection \<open> Divergence \<close>

text \<open> A divergent interaction tree infinitely performs only silent steps. \<close>

primcorec diverge :: "('e, 'r) itree" where
"diverge = \<tau> diverge"

lemma bind_diverge [simp]: "diverge \<bind> F = diverge"
  by (coinduction, auto simp add: itree.case_eq_if)

lemma unstable_diverge: "unstable diverge"
  by simp

lemma is_Ret_diverge [simp]: "is_Ret diverge = False"
  by (auto)

lemma diverge_not_Ret [dest]: "diverge = Ret v \<Longrightarrow> False"
  by (metis diverge.code itree.simps(5))

lemma is_Vis_diverge [simp]: "is_Vis diverge = False"
  by (auto)

lemma diverge_not_Vis [dest]: "diverge = Vis F \<Longrightarrow> False"
  by (metis diverge.code itree.distinct(5))

lemma diverge_not_Vis' [dest]: "Vis F = diverge \<Longrightarrow> False"
  by (metis diverge_not_Vis)

text \<open> An interaction tree is divergent if it never stabilises. \<close>

abbreviation divergent :: "('e, 's) itree \<Rightarrow> bool" ("_\<Up>" [999] 1000) where
"divergent P \<equiv> (\<not> (stabilises P))"

translations "CONST divergent P" <= "\<not> (CONST stabilises P)"

lemma diverges_implies_unstable [intro]: "divergent P \<Longrightarrow> unstable P"
  by (metis Sils.simps(1) stabilises_def)

lemma Sils_diverge: "Sils n diverge = diverge"
  by (induct n, simp_all, metis diverge.code)

lemma diverges_diverge [simp]: "divergent diverge"
  by (auto simp add: stabilises_def Sils_diverge, metis Sils_diverge Sils_injective diverge.disc_iff)

text \<open> There is a unique divergent @{type itree}. \<close>

lemma diverges_implies_equal: 
  assumes "P \<Up>" "Q \<Up>"
  shows "P = Q"
using assms proof (coinduction arbitrary: P Q rule: itree_coind')
  case RetF
  then show ?case by blast
next
  case SilF
  then show ?case by blast
next
  case VisF
  then show ?case by blast
next
  case (Ret x y)
  then show ?case
    by (meson diverges_implies_unstable itree.disc(4))
next
  case (Sil P' Q' P Q)
  then show ?case
    by (metis Sils.simps(2) stabilises_def)
next
  case (Vis F G P Q)
  then show ?case
    using diverges_implies_unstable itree.disc(6) by blast
qed

lemma Sil_cycle_diverge: "\<lbrakk> is_Sil P; un_Sil P = P \<rbrakk> \<Longrightarrow> P = diverge"
  by (coinduction arbitrary: P, auto)

lemma diverges_then_diverge: "P\<Up> \<longleftrightarrow> P = diverge"
  using diverges_diverge diverges_implies_equal by blast

lemma Sil_fp_divergent [simp]: "Sil P = P \<longleftrightarrow> P = diverge"
  by (metis Sil_cycle_diverge diverge.code diverges_diverge diverges_implies_equal itree.disc(5) itree.sel(2))

lemma Sil_nfp_stabilises [simp]: "Sil P \<noteq> P \<longleftrightarrow> stabilises P"
  by (metis Sil_fp_divergent diverges_diverge diverges_implies_equal)

lemma Sil_Sil_drop: "\<tau> (\<tau> P) = P \<Longrightarrow> \<tau> P = P"
  by (coinduction arbitrary: P, auto)
     (metis (mono_tags, lifting) itree.discI(2), metis (full_types) itree.sel(2))

lemma Sils_fp_diverge: "\<lbrakk> Sils n P = P; n > 0 \<rbrakk> \<Longrightarrow> P = diverge"
  apply (coinduction arbitrary: P, auto)
  apply (metis (mono_tags, hide_lams) gr_implies_not_zero is_Ret_Sils)
  apply (metis is_Sil_Sils)
  apply (metis (no_types, lifting) Sils_Sil_shift is_Sil_def itree.sel(2))
  done

lemma trace_of_divergent:
  assumes "P \<midarrow>t\<leadsto> P'" "divergent P"
  shows "(t, P') = ([], diverge)"
  using assms(1-2)
  apply (induct rule: trace_to.induct)
  apply (auto simp add: assms diverges_then_diverge)
  apply (metis diverge.code itree.inject(2))
  apply (metis diverge.code itree.inject(2))
  done

lemma diverge_no_Ret_trans [dest]: "diverge \<midarrow>tr\<leadsto> Ret v \<Longrightarrow> False"
  by (metis diverge_not_Ret diverges_diverge snd_conv trace_of_divergent)

lemma diverge_no_Vis_trans [dest]: "diverge \<midarrow>tr\<leadsto> Vis F \<Longrightarrow> False"
  by (metis diverge_not_Vis diverges_diverge snd_conv trace_of_divergent)

text \<open> Any interaction either stabilises to a visible event, stabilises to termination, or diverges. \<close>

lemma itree_disj_cases:
  "(\<exists> n F. P = Sils n (Vis F)) \<or> (\<exists> n x. P = Sils n (Ret x)) \<or> P = diverge"
  by (metis diverges_then_diverge is_Ret_def itree.collapse(3) itree.exhaust_disc stabilises_def)

lemma itree_cases [case_names Vis Ret diverge]:
  assumes 
    "\<And> n F. P = (Sils n (Vis F)) \<Longrightarrow> Q"
    "\<And> n x. P = (Sils n (Ret x)) \<Longrightarrow> Q"
    "P = diverge \<Longrightarrow> Q"
  shows "Q"
  by (metis assms(1) assms(2) assms(3) itree_disj_cases)

text \<open> If $P$ is not divergent, then it must be prefixed by a finite sequence of taus. \<close>

definition "no_divergence P = (\<forall> tr. \<not> P \<midarrow>tr\<leadsto> diverge)" 

lemma divergence_diverge [simp]: "no_divergence diverge = False"
  by (auto simp add: no_divergence_def)

text \<open> An @{type itree} does not diverge if every trace leads to an @{type itree} that
  stabilises. \<close>

lemma no_divergence: "no_divergence P = (\<forall>tr P'. P \<midarrow>tr\<leadsto> P' \<longrightarrow> stabilises P')"
  apply (auto simp add: no_divergence_def)
  using diverges_diverge diverges_implies_equal apply blast
  apply (meson diverges_diverge)
  done

lemma stabilises_to_no_divergence: 
  assumes "stabilises_to no_divergence P"
  shows "no_divergence P"
proof (clarsimp simp add: no_divergence)
  fix tr P'
  assume "P \<midarrow>tr\<leadsto> P'"
  hence "(\<lambda> (tr, P') P. stabilises P') (tr, P') P"
    using assms
    apply (induct rule: trace_to.induct)
      apply (auto)
    using stabilises_to.cases apply fastforce
    apply (metis Vis_Sils imageI itree.distinct(3) itree.simps(9) no_divergence pran_pdom stabilises_to.cases)
    done
  thus "stabilises P'"
    by auto
qed

lemma no_divergence_prefp_div_free:
  "stabilises_to no_divergence \<le> no_divergence"
  by (simp add: predicate1I stabilises_to_no_divergence)

lemma no_divergence_Sil: "no_divergence (Sil P) = no_divergence P"
  by (force simp add: no_divergence)

lemma no_divergence_Sils: "no_divergence (Sils n P) = no_divergence P"
  by (induct n, simp_all add: no_divergence_Sil)

lemma no_divergence_Vis: "no_divergence (Vis F) = (pran F \<subseteq> Collect no_divergence)"
  apply (auto simp add: no_divergence)
  apply (metis (no_types, lifting) image_iff pran_pdom trace_to_Vis)
  apply (metis Sils.simps(1) no_divergence stabilises_to_Sils_Vis stabilises_to_no_divergence)
  done

lemma no_divergence_stabilises_to: "no_divergence P \<Longrightarrow> stabilises_to no_divergence P"
  apply (cases P rule: itree_cases)
  apply (simp add: stabilises_alt_def' fun_eq_iff )
  apply (auto simp add: Sils_Vis_iff no_divergence_Sils no_divergence_Vis)
  done

lemma stabilises_to_is_no_diverge: "stabilises_to no_divergence = no_divergence"
  by (auto simp add: fun_eq_iff stabilises_to_no_divergence no_divergence_stabilises_to)

lemma divergent_bind: "divergent(P \<bind> Q) \<Longrightarrow> (divergent(P) \<or> (\<exists> n x. P = Sils n (Ret x) \<and> divergent(Q x)))"
  by (auto simp add: stabilises_def)
     (metis Sils_Sils bind_Ret bind_itree.disc_iff(2) itree.collapse(1))

lemma bind_divergeE [elim!]:
  assumes 
    "P \<bind> Q = diverge"
    "P = diverge \<Longrightarrow> R"
    "\<And> n x. \<lbrakk> P = Sils n (Ret x); Q x = diverge \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) assms(3) divergent_bind diverges_then_diverge)

lemma bind_divergeE' [elim!]:
  assumes 
    "diverge = P \<bind> Q"
    "P = diverge \<Longrightarrow> R"
    "\<And> n x. \<lbrakk> P = Sils n (Ret x); Q x = diverge \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) assms(3) bind_divergeE)

coinductive div_free :: "('e, 's) itree \<Rightarrow> bool" where
scons: "stabilises_to div_free P \<Longrightarrow> div_free P"

lemma div_free_Ret [simp]: "div_free (Ret x)"
  by (simp add: div_free.intros ret_stbs)

lemma div_free_Vis: "div_free (Vis F) \<longleftrightarrow> (\<forall> P \<in> pran F. div_free P)"
  by (auto simp add: div_free.intros vis_stbs)
     (metis div_free.cases itree.distinct(3) itree.distinct(5) itree.sel(3) stabilises_to.cases)

lemma div_free_Sil [simp]: "div_free (Sil P) = div_free P"
  by (metis div_free.simps is_Ret_def itree.disc(2) itree.disc(5) itree.disc(6) itree.sel(2) sil_stbs stabilises_to.cases)

lemma div_free_Sils: "div_free (Sils n P) \<longleftrightarrow> div_free P"
  by (induct n, auto)

lemma div_free_step: "\<lbrakk> P \<midarrow>[a]\<leadsto> P'; div_free P \<rbrakk> \<Longrightarrow> div_free P'"
  by (auto simp add: div_free_Vis div_free_Sils)
     (metis div_free_Sils imageI pran_pdom)

lemma div_free_diverge [simp]: "div_free diverge = False"
  by (meson div_free.simps diverges_diverge stabilises_to_stabilises)

lemma div_free_is_upto: "div_free \<le> stabilises_to div_free"
  by (meson div_free.cases predicate1I)

lemma div_free_coind:
  assumes "\<phi> P"
  and "\<phi> \<le> stabilises_to \<phi>"
  shows "div_free P"
  using assms
  apply (coinduction arbitrary: P rule: div_free.coinduct)
  apply (auto)
  apply (metis (mono_tags, lifting) mono_stabilises_to predicate1I rev_predicate1D)
  done

lemma div_free_coinduct:
  assumes "\<phi> P"
  "\<phi> diverge \<Longrightarrow> False"
  "\<And> n F e. \<lbrakk> \<phi> (Sils n (Vis F)); e \<in> pdom(F) \<rbrakk> \<Longrightarrow> \<phi> (F e)"
  shows "div_free P"
proof (rule div_free_coind[of \<phi>, OF assms(1)], safe)
  fix P
  assume \<phi>P: "\<phi> P"
  show "stabilises_to \<phi> P"
  proof (cases P rule: itree_cases)
    case (Vis e G)
    then show ?thesis
      by (simp, metis (no_types, lifting) \<phi>P assms(3) image_subset_iff mem_Collect_eq pran_pdom)
  next
    case (Ret n x)
    then show ?thesis
      by (metis (mono_tags, hide_lams) stabilises_to_Sils_RetI) 
  next
    case diverge
    then show ?thesis
      by (metis \<phi>P assms(2))
  qed
qed
  
lemma div_free_run: "div_free (run E)"
  apply (coinduction rule: div_free_coinduct)
  apply (metis (no_types, hide_lams) is_Vis_diverge run.disc_iff)
  apply (metis Vis_Sils map_pfun_apply pdom_map_pfun run.code)
  done

lemma no_divergence_in_div_free: "no_divergence \<le> div_free"
  apply (auto)
  apply (rule div_free_coind[of "no_divergence"])
   apply (auto simp add: stabilises_to_is_no_diverge)
  done

lemma trace_to_Nil_diverges: "P \<midarrow>[]\<leadsto> diverge \<Longrightarrow> divergent P"
  using Sils_diverge diverges_then_diverge trace_to_Nil_Sils by force

lemma trace_to_div_free: "P \<midarrow>tr\<leadsto> P' \<Longrightarrow> div_free P \<Longrightarrow> div_free P'"
  apply (induct tr arbitrary: P)
  apply (metis div_free_Sils trace_to_Nil_Sils)
  apply (erule trace_to_ConsE)
  apply (auto)
  apply (metis Vis_Cons_trns div_free_Sils div_free_step trace_of_Sils)
  done

lemma div_free_in_no_divergence: "div_free \<le> no_divergence"
  by (auto, metis div_free_diverge diverges_diverge diverges_implies_equal no_divergence trace_to_div_free)
  
lemma div_free_is_no_divergence: "div_free = no_divergence"
  by (simp add: antisym div_free_coind div_free_in_no_divergence predicate1I stabilises_to_is_no_diverge)

lemma div_free_no_min_divergence: "div_free P \<Longrightarrow> \<not> P \<midarrow>t\<leadsto> diverge"
  by (simp add: div_free_is_no_divergence no_divergence_def)

lemma divergent_trace_toI: "\<lbrakk> \<And> P'. P \<midarrow>[]\<leadsto> P' \<Longrightarrow> unstable P' \<rbrakk> \<Longrightarrow> divergent P"
  by (metis stabilises_def trace_of_Sils)

lemma div_free_bindI: "\<lbrakk> div_free P; \<forall> x \<in> \<^bold>R(P). div_free (Q x) \<rbrakk> \<Longrightarrow> div_free (P \<bind> Q)"
  by (auto elim!: trace_to_bindE simp add: div_free_is_no_divergence no_divergence_def retvals_def)
     (metis trace_of_Sils trace_to_Nil trace_to_trans)

lemma div_free_bind: "div_free (P \<bind> Q) \<longleftrightarrow> (div_free P \<and> (\<forall> x \<in> \<^bold>R(P). div_free (Q x)))" 
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  thus ?rhs
    by (simp add: div_free_is_no_divergence no_divergence_def retvals_def)
       (metis bind_diverge trace_to_bind trace_to_bind_left)
next
  assume ?rhs
  thus ?lhs
    by (simp add: div_free_bindI)
qed

lemma initev_diverge [simp]: "\<^bold>I(diverge) = {}"
  by (auto simp add: initev_def)
     (metis Sils_diverge Sils_injective diverge_not_Vis)

lemma retvals_diverge [simp]: "\<^bold>R(diverge) = {}"
  by (auto simp add: retvals_def)

lemma evalpha_diverge [simp]: "\<^bold>A(diverge) = {}"
  by (auto simp add: evalpha_def)
     (meson diverges_diverge stabilises_traceI)

subsection \<open> Removing Leading Silent Steps \<close>

definition "un_Sils P = (if (stabilises P) then (THE P'. \<exists> n. P = Sils n P' \<and> stable P') else P)"

lemma un_Sils_Ret [simp]: "un_Sils (Ret x) = Ret x"
  by (simp add: un_Sils_def, rule the_equality, auto)

lemma un_Sils_Vis [simp]: "un_Sils (Vis F) = Vis F"
  by (simp add: un_Sils_def, rule the_equality, auto)
     (metis Sils.simps(1), metis Sils_0 is_Vis_Sils itree.disc(9))

lemma un_Sils_Sil [simp]: "un_Sils (Sil P) = un_Sils P"
proof (cases "P = diverge")
  case True
  then show ?thesis
    by (metis diverge.code)
next
  case False
  hence "stabilises P"
    using diverges_then_diverge by auto
  then show ?thesis
    by (auto simp add: un_Sils_def)
       (metis (mono_tags, hide_lams) Sils.simps(1) Sils.simps(2) itree.disc(5) itree.sel(2) un_Sil_Sils)
qed

lemma un_Sils_Sils [simp]: "un_Sils (Sils n P) = un_Sils P"
  by (induct n, simp_all)

lemma stable_un_Sils [simp]: "stable P \<Longrightarrow> un_Sils (Sils n P) = P"
  by (auto simp add: un_Sils_def, meson stabilises_def)

lemma diverge_un_Sils [simp]: "un_Sils diverge = diverge"
  by (simp add: un_Sils_def)

subsection \<open> Strong Traces \<close>

inductive strace_to :: "('a, 'b) itree \<Rightarrow> 'a option list \<Rightarrow> ('a, 'b) itree \<Rightarrow> bool" ("_ \<midarrow>_\<rightarrow> _" [55, 0, 55] 55) where
strace_to_Nil [intro!]: "P \<midarrow>[]\<rightarrow> P" | 
strace_to_Sil [intro!]: "P \<midarrow>tr\<rightarrow> P' \<Longrightarrow> Sil P \<midarrow>None # tr\<rightarrow> P'" |
strace_to_Vis [intro!]: "\<lbrakk> e \<in> pdom F; F e \<midarrow>tr\<rightarrow> P' \<rbrakk> \<Longrightarrow> Vis F \<midarrow>Some e # tr\<rightarrow> P'"

inductive_cases
  strace_NilE [elim!]: "P \<midarrow>[]\<rightarrow> P'" and
  strace_Cons_NoneE [elim!]: "P \<midarrow>None # tr\<rightarrow> P'" and
  strace_Cons_SomeE [elim!]: "P \<midarrow>Some e # tr\<rightarrow> P'"

lemma strace_to_Sils [intro!]: "P \<midarrow>tr\<rightarrow> P' \<Longrightarrow> Sils n P \<midarrow>(replicate n None) @ tr\<rightarrow> P'"
  by (induct n, auto)

lemma trace_then_strace:
  assumes "P \<midarrow>tr\<leadsto> P'"
  shows "(\<exists> tr'. P \<midarrow>tr'\<rightarrow> P' \<and> tr = [x. Some x \<leftarrow> tr'])"
using assms proof (induct tr arbitrary: P)
  case Nil
  then obtain n where "P = Sils n P'"
    by (meson trace_to_NilE)
  then show ?case
    using strace_to_Nil strace_to_Sils by fastforce
next
  case (Cons a tr)
  then obtain n F where P: "P = Sils n (Vis F)" "a \<in> pdom(F)"
    by (meson trace_to_ConsE trace_to_singleE)
  moreover then obtain tr' where tr': "F a \<midarrow>tr'\<rightarrow> P'" "tr = [x. Some x \<leftarrow> tr']"
    using Cons.hyps Cons.prems by auto
  ultimately show ?case
    by (rule_tac x="replicate n None @ Some a # tr'" in exI, auto)
qed

lemma strace_then_trace:
  assumes "P \<midarrow>tr\<rightarrow> P'" 
  shows "P \<midarrow>[x. Some x \<leftarrow> tr]\<leadsto> P'"
using assms by (induct rule: strace_to.induct, auto)

lemma strace_to_ConsE:
  assumes "P \<midarrow>x # xs\<rightarrow> Q" 
  obtains P' where "P \<midarrow>[x]\<rightarrow> P'" "P' \<midarrow>xs\<rightarrow> Q"
  using assms 
proof -
  have "\<And> tr. P \<midarrow>tr\<rightarrow> Q \<Longrightarrow> tr \<noteq> [] \<longrightarrow> (\<exists>P'. P \<midarrow>[hd tr]\<rightarrow> P' \<and> P' \<midarrow>tl tr\<rightarrow> Q)"
  proof -
    fix tr
    assume "P \<midarrow>tr\<rightarrow> Q"
    thus "tr \<noteq> [] \<longrightarrow> (\<exists>P'. P \<midarrow>[hd tr]\<rightarrow> P' \<and> P' \<midarrow>tl tr\<rightarrow> Q)"
      by (induct rule: strace_to.induct, auto)
  qed
  thus ?thesis
    by (metis assms list.distinct(1) list.sel(1) list.sel(3) that)
qed

lemma strace_to_bind_cases:
  assumes 
    "(P \<bind> Q) \<midarrow>tr\<rightarrow> Q'"
  shows "(\<exists> P'. P \<midarrow>tr\<rightarrow> P' \<and> Q' = (P' \<bind> Q)) 
          \<or> (\<exists> x tr\<^sub>1 tr\<^sub>2. P \<midarrow>tr\<^sub>1\<rightarrow> Ret x \<and> Q x \<midarrow>tr\<^sub>2\<rightarrow> Q' \<and> tr = tr\<^sub>1 @ tr\<^sub>2)"
  using assms proof (induct tr arbitrary: P Q Q')
  case Nil
  then show ?case by (auto elim: strace_NilE)
next
  case (Cons a tr)
  then show ?case
    oops

subsection \<open> Power \<close>

overloading
  itreepow \<equiv> "compow :: nat \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree"
begin

fun itreepow :: "nat \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"itreepow 0 P = Ret" |
"itreepow (Suc n) P = P \<Zcomp> itreepow n P"

end

locale itreepow_chain =
  fixes n P s s' m ss
  assumes length_ss: "length ss = n + 1"
  and init_st: "ss ! 0 = (0, s)"
  and last_st: "snd (ss ! n) = s'"
  and ss_iter: "\<forall> i < (length ss - 1). P (snd (ss ! i)) = Sils (fst (ss ! (i + 1))) (Ret (snd (ss ! (i + 1))))"
  and sil_count: "m = sum_list (map fst ss)"

text \<open> @{const itreepow_chain} is used to characterise that an ITree @{term P} started in state
  @{term s}, and iterated @{term n} times, terminates in a particular state. This is shown through
  a list @{term ss}, whose elements are pairs @{term "(n, x)"} giving the number of silent events
  and return values produced in each iteration. In particular, @{term ss} characterises a minimal
  loop invariant for the iteration. \<close>

locale itree_chain =
  fixes P :: "('e, 's) htree" \<comment> \<open> The loop body \<close>
  and s s' :: "'s" \<comment> \<open> Initial and final state \<close>
  and chn :: "('e list \<times> 's) list" \<comment> \<open> The chain \<close>
  assumes length_chain: "length chn > 0" 
  and last_st: "snd (last chn) = s'"
  and chain_start: "P s \<midarrow>fst (hd chn)\<leadsto> Ret (snd (hd chn))"
  and chain_iter: "\<forall> i < length chn - 1. P (snd (chn ! i)) \<midarrow>fst (chn ! (i + 1))\<leadsto> Ret (snd (chn ! (i + 1)))"

lemma itreepow_Sils_Ret_dest:
  fixes P :: "('e, 's) htree"
  assumes "(P ^^ n) s = Sils m (Ret s')"
  shows "\<exists> ss. itreepow_chain n P s s' m ss"
using assms proof (induct n arbitrary: m s s')
  case 0
  then show ?case 
    by (rule_tac x="[(0, s)]" in exI, unfold_locales, auto)
next
  case (Suc n)
  from Suc(2) obtain m\<^sub>0 s\<^sub>0 where P: "P s = Sils m\<^sub>0 (Ret s\<^sub>0)" "m\<^sub>0 \<le> m" and Pn: "(P ^^ n) s\<^sub>0 = Sils (m - m\<^sub>0) (\<cmark> s')"
    by (auto elim!: bind_SilsE simp add: kleisli_comp_def)
  obtain ss\<^sub>0 where "itreepow_chain n P s\<^sub>0 s' (m - m\<^sub>0) ss\<^sub>0"
    by (meson Pn Suc.hyps)
  then interpret ipow: itreepow_chain n P s\<^sub>0 s' "m - m\<^sub>0" ss\<^sub>0
    by simp
    
  let ?ss = "(0, s) # (m\<^sub>0, s\<^sub>0) # tl ss\<^sub>0"

  from P(2) show ?case
    apply (rule_tac x="?ss" in exI, unfold_locales, auto simp add: ipow.length_ss)
    apply (metis add.left_neutral dual_order.antisym hd_Cons_tl ipow.init_st ipow.last_st ipow.length_ss le_add1 length_0_conv nth_Cons' snd_conv)
    apply (smt (verit, ccfv_threshold) P(1) add.commute add_diff_cancel_left' hd_Cons_tl ipow.init_st ipow.length_ss ipow.ss_iter length_0_conv less_Suc_eq less_Suc_eq_0_disj nat.simps(3) nth_Cons_0 nth_Cons_pos plus_1_eq_Suc prod.sel(1) snd_conv)
    apply (metis (no_types, lifting) Suc_eq_plus1 add.left_neutral add_diff_cancel_left' eq_diff_iff fst_conv hd_Cons_tl ipow.init_st ipow.length_ss ipow.sil_count le_add1 length_0_conv list.simps(9) nat.simps(3) nth_Cons_0 sum_list.Cons)
    done
qed
  
subsection \<open> Iteration \<close>

text \<open> For now we support only basic tail-recursive iteration. \<close>

corec iterate :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"iterate b P s = (if (b s) then (P s \<bind> (\<tau> \<circ> (iterate b P))) else Ret s)"

abbreviation "loop \<equiv> iterate (\<lambda> s. True)"

abbreviation "iter P \<equiv> loop (\<lambda> _. P) ()"

lemma iterate_cond_false [simp]:
  "\<not> (b s) \<Longrightarrow> iterate b P s = Ret s"
  by (simp add: iterate.code)

lemma iterate_body_nonterminates:
  assumes "nonterminates (P s)" "b s"
  shows "nonterminates (iterate b P s)"
  by (simp add: assms iterate.code)

lemma loop_unfold: "loop P = P \<Zcomp> (\<tau> \<circ> loop P)"
  by (simp add: kleisli_comp_def fun_eq_iff iterate.code)

lemma loop_Ret: "loop Ret = (\<lambda> s. diverge)"
  by (metis Sil_nfp_stabilises bind_Ret comp_apply diverges_then_diverge iterate.code)

lemma iterate_Ret_dest:
  "Ret x = iterate b P s \<Longrightarrow> (\<not> (b s) \<and> x = s)"
  apply (cases "P s")
  apply (metis bind_Ret comp_apply iterate.code itree.distinct(1) itree.sel(1))
  apply (metis bind_itree.disc_iff(1) iterate.code itree.disc(2) itree.discI(1) itree.inject(1))
  apply (metis bind_Vis iterate.code itree.distinct(3) itree.inject(1))
  done

lemma iterate_RetE:
  assumes "iterate b P s = Ret x" "\<lbrakk> \<not> (b s); x = s \<rbrakk> \<Longrightarrow> Q"
  shows Q
  by (metis assms iterate_Ret_dest)

lemma iterate_RetE':
  assumes "Ret x = iterate b P s" "\<lbrakk> \<not> (b s); x = s \<rbrakk> \<Longrightarrow> Q"
  shows Q
  by (metis assms iterate_Ret_dest)

lemma iterate_Sil_dest: 
  "\<tau> P' = iterate b P s \<Longrightarrow> (b s \<and> ((\<exists> s'. P s = Ret s' \<and> P' = iterate b P s') \<or> (\<exists> P''. P s = \<tau> P'' \<and> P' = (P'' \<bind> \<tau> \<circ> iterate b P))))"
  apply (cases "P s")
  apply (simp_all)
  apply (metis bind_Ret comp_apply iterate.code itree.distinct(1) itree.sel(2))
  apply (metis bind_Sil iterate.code itree.distinct(1) itree.inject(2))
  apply (metis bind_Vis iterate.code itree.distinct(1) itree.distinct(5))
  done

lemma iterate_SilE:
  assumes "\<tau> P = iterate b Q s"
    "\<And> s'. \<lbrakk> b s; Q s = Ret s'; P = iterate b Q s' \<rbrakk> \<Longrightarrow> R"
    "\<And> P'. \<lbrakk> b s; Q s = \<tau> P' \<and> P = (P' \<bind> \<tau> \<circ> iterate b Q) \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms iterate_Sil_dest)

lemma iterate_Vis_dest:
  "Vis F = iterate b Q s \<Longrightarrow> b s \<and> (\<exists> G. Q s = Vis G \<and> F = (map_pfun (\<lambda> x. bind_itree x (\<tau> \<circ> iterate b Q)) G))"
  apply (cases "Q s")
  apply (simp_all)
  apply (metis bind_Ret comp_apply iterate.code itree.simps(7) itree.simps(9))
  apply (metis bind_Sil iterate.code itree.distinct(3) itree.distinct(5))
  apply (metis bind_Vis iterate.code itree.inject(3) itree.simps(7))
  done

lemma iterate_VisE:
  assumes "Vis F = iterate b Q s"
    "\<And> G. \<lbrakk> b s; Q s = Vis G; F = (map_pfun (\<lambda> x. bind_itree x (\<tau> \<circ> iterate b Q)) G) \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis assms(1) assms(2) iterate_Vis_dest)

lemma 
  assumes "itreepow_chain n P s s' m ss" "\<forall> i\<in>{1..n}. fst (ss ! i) > 0" "\<not> b (snd (ss ! n))" "\<forall> i<n. b(snd (ss ! i))"
  shows "Sils m (Ret s') = iterate b P s"
using assms proof (coinduction arbitrary: ss n s s' m rule: itree_coind')
  case RetF
  then interpret ipow: itreepow_chain n P s s' m ss by simp
  from RetF(2-) ipow.sil_count show ?case
    apply (auto)
    apply (metis Suc_leI add.right_neutral atLeastAtMost_iff ipow.init_st ipow.length_ss iterate.code itree.discI(1) le_add1 less_add_same_cancel1 less_numeral_extra(1) neq0_conv nth_mem snd_conv)
    apply (metis One_nat_def RetF(4) add.commute fst_conv in_set_conv_nth ipow.init_st ipow.length_ss is_Ret_def iterate_RetE less_Suc_eq less_nat_zero_code neq0_conv plus_1_eq_Suc snd_conv)
    done
next
  case SilF
  then interpret ipow: itreepow_chain n P s s' m ss by simp
  from SilF(2-) ipow.sil_count show ?case
    apply (auto simp add: is_Sil_Sils)
     apply (smt (z3) SilF(1) Suc_leI Suc_length_conv add.commute add.right_neutral add_diff_cancel_right' atLeastAtMost_iff bind_itree.disc_iff(2) fst_conv ipow.init_st ipow.length_ss is_Sil_Sils iterate.code itreepow_chain.ss_iter length_0_conv length_map list.simps(9) neq0_conv nth_Cons_0 plus_1_eq_Suc snd_conv sum_list.Cons sum_list.Nil zero_less_one)
    apply (metis Suc_leI atLeastAtMost_iff elem_le_sum_list ipow.init_st ipow.length_ss iterate.code itree.disc(4) length_map less_add_same_cancel1 less_numeral_extra(1) not_gr0 not_less nth_map snd_conv)
    done
next
  case VisF
  then interpret ipow: itreepow_chain n P s s' m ss by simp
  from VisF(2-) show ?case
    by (auto, metis One_nat_def Suc_eq_plus1 Suc_le_eq atLeastAtMost_iff bind_Sil diff_Suc_Suc diff_zero ipow.init_st ipow.length_ss ipow.ss_iter is_Sil_Sils is_Sil_def iterate.code itree.collapse(3) itree.distinct(3) itree.distinct(5) le_add1 not0_implies_Suc plus_1_eq_Suc snd_conv)
next
  case Ret
  then interpret ipow: itreepow_chain n P s s' m ss by simp
  from Ret(2-) show ?case
    by (auto, metis Ret(1) Ret_Sils_iff gr_implies_not0 ipow.init_st ipow.last_st iterate_RetE linorder_neqE_nat snd_conv)
next
  case (Sil P' Q)
  then interpret ipow: itreepow_chain n P s s' m ss by simp
  have ngz: "n > 0"
    by (metis Sil(2) Sil(5) gr0I ipow.init_st iterate.code itree.disc(4) itree.disc(5) snd_conv)
  from Sil(1,2,4-) ngz show ?case
    apply (auto elim!:iterate_SilE)
    apply (metis One_nat_def Suc_eq_plus1 Suc_leI add.right_neutral atLeastAtMost_iff diff_Suc_Suc diff_zero ipow.init_st ipow.length_ss ipow.ss_iter is_Ret_Sils itree.discI(1) le_add1 less_numeral_extra(3) snd_conv)
    apply (rule_tac x="hd ss # (fst (ss ! 1) - 1, snd (ss ! 1)) # tl (tl ss)" in exI)
    apply (rule_tac x="n" in exI)
    apply (rule_tac x="s" in exI)
    apply (rule_tac x="s'" in exI)
    apply (rule_tac x="m-1" in exI)
    apply (auto)
    oops

(*
  next
  case Vis
then show ?case sorry
qed
  case wform
  then show ?case
  proof (cases "n = 0")
    case True 
    with wform show ?thesis 
      apply (auto simp add: iterate.code in_set_conv_nth)
      apply (metis (no_types, hide_lams) One_nat_def Suc_pred add.right_neutral add_diff_cancel_left' fst_conv hd_Cons_tl is_Sil_Sils itree.disc(4) length_0_conv length_tl list.simps(8) list.simps(9) nat.simps(3) nth_Cons_0 sum_list.Cons sum_list.Nil)
      done
    oops
*)

lemma itree_chan_singleton_dest [dest!]: 
  assumes "itree_chain P s s' [x]" 
  shows "P s \<midarrow>fst x\<leadsto> \<cmark> s' \<and> snd x = s'"
proof -
  interpret chn: itree_chain P s s' "[x]"
    by (simp add: assms)
  from chn.chain_start show ?thesis
    using chn.last_st by auto
qed

lemma itree_chain_Cons_dest:
  assumes "itree_chain P s s' ((es\<^sub>1, s\<^sub>0) # chn)" "length chn > 0"
  shows "itree_chain P s\<^sub>0 s' chn"
proof -
  interpret chn: itree_chain P s s' "(es\<^sub>1, s\<^sub>0) # chn"
    by (simp add: assms)
  from assms(2) show ?thesis
    apply (unfold_locales, auto)
    using chn.last_st apply auto[1]
    using chn.chain_iter hd_conv_nth apply fastforce
    apply (metis (no_types, hide_lams) One_nat_def Suc_eq_plus1 Suc_less_eq Suc_pred assms(2) chn.chain_iter diff_Suc_Suc diff_zero list.size(4) nth_Cons_Suc)
    done
qed

lemma trace_to_Sil_dest [dest]: "P \<midarrow>tr\<leadsto> \<tau> P' \<Longrightarrow> P \<midarrow>tr\<leadsto> P'"
  by (metis append.right_neutral trace_to_Nil trace_to_Sil trace_to_trans)

lemma iterate_trace_to:
  assumes "P s \<midarrow>es \<leadsto> Ret s'" "b s"
  shows "iterate b P s \<midarrow>es\<leadsto> iterate b P s'"
proof -
  have "(P s \<bind> \<tau> \<circ> iterate b P) \<midarrow>es\<leadsto> (Ret s' \<bind> \<tau> \<circ> iterate b P)"
    by (meson assms(1) trace_to_bind_left)
  thus ?thesis
    by (auto simp add: iterate.code assms)
qed

lemma iterate_term_once:
  assumes "P s \<midarrow>es \<leadsto> Ret s'" "b s" "\<not> b s'"
  shows "iterate b P s \<midarrow>es\<leadsto> Ret s'"
  by (metis assms(1) assms(2) assms(3) iterate.code iterate_trace_to)

lemma iterate_chain_terminates:
  assumes "itree_chain P s s' chn" "b s" "\<forall> i < length chn - 1. b (snd (chn ! i))" "\<not> b s'"
  shows "iterate b P s \<midarrow>concat (map fst chn)\<leadsto> Ret s'"
using assms proof (induct chn arbitrary: s)
  case Nil
  then interpret chn: itree_chain P s s' "[]"
    by simp
  show ?case
    using chn.length_chain by blast    
next
  case (Cons ec chn)
  show ?case
  proof (cases "chn = []")
    case True
    thus ?thesis
      using Cons by (auto, meson iterate_term_once)
  next
    case False
    then interpret chn: itree_chain P s s' "ec # chn"
      by (simp add: Cons.prems(1))
    have chn': "itree_chain P (snd ec) s' chn"
      by (metis Cons.prems(1) False itree_chain_Cons_dest length_greater_0_conv prod.exhaust_sel)
    have "P s \<midarrow>fst ec\<leadsto> Ret (snd ec)"
      using chn.chain_start by auto
    hence "iterate b P s \<midarrow>fst ec\<leadsto> iterate b P (snd ec)"
      by (simp add: Cons.prems(2) iterate_trace_to)
    moreover have "b (snd ec)"
      by (metis Cons.prems(3) chn' itree_chain.length_chain length_tl list.sel(3) nth_Cons_0)
    ultimately show ?thesis
      apply (simp, rule_tac trace_to_trans)
       apply (auto)
      apply (metis Cons.hyps Cons.prems(3) One_nat_def Suc_eq_plus1 Suc_pred assms(4) chn' diff_Suc_1 itree_chain_def list.size(4) not_less_eq nth_Cons_Suc)
      done
  qed
qed

lemma iterate_body_Ret:
  assumes "iterate b P s \<midarrow>[]\<leadsto> Ret s'" "b s"
  obtains s\<^sub>0 where "P s \<midarrow>[]\<leadsto> Ret s\<^sub>0"
  using assms
  by (auto elim!: bind_RetE trace_to_bindE simp add: iterate.code)

lemma iterate_body_countdown:
  assumes "iterate b P s = Sils n (\<cmark> s')" "b s"
  obtains m s\<^sub>0 where "0 < n" "m \<le> n" "P s = Sils m (Ret s\<^sub>0)" "iterate b P s\<^sub>0 = Sils (n - m - 1) (\<cmark> s')"
proof -
  from assms obtain m s\<^sub>0 where "m \<le> n" "P s = Sils m (\<cmark> s\<^sub>0)" "Sil (iterate b P s\<^sub>0) = Sils (n - m) (\<cmark> s')"
    by (auto elim!: bind_SilsE simp add: iterate.code)
  moreover have "0 < n"
    by (metis Sils.simps(1) assms gr0I iterate_RetE)
  moreover have "iterate b P s\<^sub>0 = Sils (n - m - 1) (\<cmark> s')"
    by (metis Ret_Sils_iff calculation(3) itree.sel(2) itree.simps(5) un_Sil_Sils)
  ultimately show ?thesis using that by auto
qed

lemma iterate_body_consume:
  assumes "iterate b P s \<midarrow>tr\<leadsto> \<cmark> s'" "b s"
  obtains tr\<^sub>0 s\<^sub>0 where "tr\<^sub>0 \<le> tr" "P s \<midarrow>tr\<^sub>0\<leadsto> \<cmark> s\<^sub>0" "iterate b P s\<^sub>0 \<midarrow>tr - tr\<^sub>0\<leadsto> \<cmark> s'"
  using assms 
  by (auto elim!: trace_to_bindE simp add: iterate.code)
     (metis Prefix_Order.prefixI append_minus)

lemma iterate_body_strong_consume:
  assumes "iterate b P s \<midarrow>tr\<rightarrow> \<cmark> s'" "b s"
  obtains tr\<^sub>0 s\<^sub>0 where "tr\<^sub>0 < tr" "P s \<midarrow>tr\<^sub>0\<rightarrow> \<cmark> s\<^sub>0" "iterate b P s\<^sub>0 \<midarrow>tr - tr\<^sub>0\<rightarrow> \<cmark> s'"
  oops

lemma iterate_ncond_prop:
  "\<not> (b s) \<Longrightarrow> ((\<lambda>s. if b s then P s \<bind> (\<lambda>s'. \<tau> (\<cmark> s')) else \<cmark> s) ^^ n) s = Ret s"
  by (induct n, auto simp add: kleisli_comp_def)

lemma iterate_chain:
  fixes P :: "('e, 's) htree"
  assumes "\<exists> m\<ge>n. iterate b P s = Sils m (\<cmark> s')" "b s"
  shows "\<exists> chn. itree_chain P s s' chn"
  oops

lemma iterate_as_power:
  fixes P :: "('e, 's) htree"
  assumes "\<exists> m\<le>n. iterate b P s = Sils m (\<cmark> s')" "b s"
  shows "iterate b P s = ((\<lambda> s. (if (b s) then (P s \<bind> (\<lambda> s'. \<tau> (Ret s'))) else Ret s)) ^^ n) s"
using assms proof (induct n arbitrary: s)
  case 0
  then show ?case by (meson iterate_body_countdown not_less)
next
  case (Suc n)
  obtain n' where n': "n'\<le>Suc n" "iterate b P s = Sils n' (\<cmark> s')"
    using Suc.prems(1) by blast
  obtain m s\<^sub>0 where P: "0 < n'" "m \<le> n'" "P s = Sils m (\<cmark> s\<^sub>0)" "iterate b P s\<^sub>0 = Sils (n' - m - 1) (\<cmark> s')"
    by (meson Suc.prems(2) iterate_body_countdown n'(2))
  have "iterate b P s = \<tau> (Sils m (iterate b P s\<^sub>0))"
    by (subst iterate.code, simp add: Suc(3) P)
  have le_n: "n' - m - 1 \<le> n"
    using n'(1) by auto
  show ?case
  proof (cases "b s\<^sub>0")
    case True
    hence hyp: "iterate b P s\<^sub>0 = ((\<lambda>s. (if b s then (P s \<bind> (\<lambda> s'. \<tau> (Ret s'))) else \<cmark> s)) ^^ n) s\<^sub>0"
      using P(4) Suc.hyps le_n by blast
    show ?thesis
      by (simp add: iterate.code Suc kleisli_comp_def, simp add: P(3) hyp)
  next
    case False
    then show ?thesis 
      by (simp add: iterate.code Suc kleisli_comp_def P(3) iterate_ncond_prop)
  qed
qed

thm nat_less_induct

thm nat.induct

lemma 
  assumes "iterate b P s \<midarrow>tr\<rightarrow> \<cmark> x"
  shows "\<exists> chn. itree_chain P s s' chn \<and> concat (map fst chn) = es"
using assms proof (induct "length tr" arbitrary: tr s rule: nat_less_induct)
  case 1
  
  then show ?case
    oops

lemma assumes "iterate b P s = Sils n (Ret s')"
  shows "\<exists> m. iterate b P s = (P ^^ m) s"
  using assms
  oops  


lemma 
  assumes "iterate b P s \<midarrow>es\<leadsto> Ret s'"
  shows "\<exists> chn. itree_chain P s s' chn \<and> concat (map fst chn) = es"
using assms proof (induct es)
  case Nil
  then show ?case 
    (* Need to induct on the number of Sils *)
    oops

lemma 
  assumes 
    "(P ^^ n) s \<midarrow>[]\<leadsto> Ret s'" "\<not> b s'"
    "\<forall> m < n. \<forall> s''. (P ^^ m) s \<midarrow>[]\<leadsto> Ret s'' \<longrightarrow> b s''"
  shows "iterate b P s \<midarrow>[]\<leadsto> Ret s'"
  oops


lemma 
  assumes 
    "(P ^^ n) s \<midarrow>es\<leadsto> Ret s'" "\<not> b s'"
    "\<forall> m < n. \<forall> es' s''. (P ^^ m) s \<midarrow>es'\<leadsto> Ret s'' \<longrightarrow> b s''"
  shows "iterate b P s \<midarrow>es\<leadsto> Ret s'"
  oops

lemma "iterate b P s \<midarrow>tr\<leadsto> Ret s' \<Longrightarrow> 
       (\<exists> n>0. \<exists> es rs. 
            length es = n \<comment> \<open> Each iteration's traces \<close>
          \<and> length rs = (n+1) \<comment> \<open> Each iteration's return values \<close>
          \<and> tr = concat es
          \<and> rs ! 0 = s
          \<and> (\<forall> i < n. b (rs ! i))
          \<and> rs ! (n - 1) = s'
          \<and> (\<forall> i \<in> {1..n}. P (rs ! (i - 1)) \<midarrow>es ! (i - 1)\<leadsto> Ret (rs ! i)))"
  oops
  

end