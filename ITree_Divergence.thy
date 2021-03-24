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

text \<open> An @{type itree} stabilises to a relation @{term R} if after stabilising and choosing a 
  new event, the continuation is in @{term R}. \<close>

inductive stabilises_to :: "(('e, 's) itree \<Rightarrow> bool) \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" where
ret_stbs [intro]: "stabilises_to R (Ret x)" |
sil_stbs [intro]: "stabilises_to R P \<Longrightarrow> stabilises_to R (Sil P)" |
vis_stbs [intro]: "(\<And> t. t \<in> ran F \<Longrightarrow> R t) \<Longrightarrow> stabilises_to R (Vis F)"

lemma monotonic_stabilises_to: "stabilises_to R P \<Longrightarrow> R \<le> S \<Longrightarrow> stabilises_to S P"
  apply (induct rule: stabilises_to.induct)
  apply (simp_all add: ret_stbs sil_stbs vis_stbs)
  apply (simp add: predicate1D vis_stbs)
  done

lemma mono_stabilises_to [mono add]: "R \<le> S \<Longrightarrow> stabilises_to R \<le> stabilises_to S"
  using monotonic_stabilises_to by auto

lemma stabilises_to_stabilises [intro]: "stabilises_to R P \<Longrightarrow> stabilises P"
  by (induct rule: stabilises_to.induct, auto)

lemma stabilises_to_Sils_VisI [intro]: "ran F \<subseteq> Collect R \<Longrightarrow> stabilises_to R (Sils n (Vis F))"
  by (induct n, auto)

lemma stabilises_to_Sils_RetI [intro]: "stabilises_to R (Sils n (Ret x))"
  by (induct n, auto)

lemma stabilises_alt_def: 
  "stabilises_to R P = (\<exists> n P'. Sils n P' = P \<and> ((P' \<in> range Vis \<and> ran (un_Vis P') \<subseteq> Collect R) \<or> P' \<in> range Ret))"
  apply (auto)
   apply (induct rule: stabilises_to.induct)
  apply (auto)
  apply (meson Sils.simps(1) range_eqI)
  apply (metis Sils.simps(2) itree.sel(3) rangeI)
  apply (meson Sils.simps(2) rangeI)
  apply (smt (z3) Collect_mono_iff Sils.simps(1) itree.sel(3) mem_Collect_eq ran_def rangeI)
  done

lemma stabilises_alt_def': 
  "stabilises_to R P = 
    ((\<exists> n F. Sils n (Vis F) = P \<and> ran F \<subseteq> Collect R) \<or> (\<exists> n x. Sils n (Ret x) = P))"
  by (auto simp add: stabilises_alt_def, metis itree.sel(3) rangeI, blast)
  
lemma stabilises_to_Sils_Vis [simp]: "stabilises_to R (Sils n (Vis F)) = (ran F \<subseteq> Collect R)"
  by (auto, auto simp add: Sils_Vis_iff stabilises_alt_def, metis Sils_Vis_not_Ret)

subsection \<open> Divergence \<close>

text \<open> A divergent interaction tree infinitely performs only silent steps. \<close>

primcorec diverge :: "('e, 'r) itree" where
"diverge = Sil diverge"

lemma bind_diverge: "diverge \<bind> F = diverge"
  by (coinduction, auto simp add: itree.case_eq_if)

lemma unstable_diverge: "unstable diverge"
  by simp

text \<open> An interaction tree is divergent if it never stabilises. \<close>

abbreviation "divergent P \<equiv> (\<not> (stabilises P))"

translations "CONST divergent P" <= "\<not> (CONST stabilises P)"

lemma diverges_implies_unstable [intro]: "divergent P \<Longrightarrow> unstable P"
  by (metis Sils.simps(1) stabilises_def)

lemma Sils_diverge: "Sils n diverge = diverge"
  by (induct n, simp_all, metis diverge.code)

lemma diverges_diverge [simp]: "divergent diverge"
  by (auto simp add: stabilises_def Sils_diverge, metis Sils_diverge Sils_injective diverge.disc_iff)

text \<open> There is a unique divergent @{type itree}. \<close>

lemma diverges_implies_equal: 
  assumes "divergent P" "divergent Q"
  shows "P = Q"
using assms proof (coinduction arbitrary: P Q rule: itree_coind)
  case (wform P Q)
  then show ?case
    by blast
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

lemma diverges_then_diverge: "divergent P \<longleftrightarrow> P = diverge"
  using diverges_diverge diverges_implies_equal by blast

lemma trace_of_divergent:
  assumes "P \<midarrow>t\<leadsto> P'" "divergent P"
  shows "(t, P') = ([], diverge)"
  using assms(1-2)
  apply (induct rule: trace_to.induct)
  apply (auto simp add: assms diverges_then_diverge)
  apply (metis diverge.code itree.inject(2))
  apply (metis diverge.code itree.inject(2))
  done

text \<open> Any interaction either stabilises to a visible event, stabilises to termination, or diverges. \<close>

lemma itree_disj_cases:
  "(\<exists> n F. P = Sils n (Vis F)) \<or> (\<exists> n x. P = Sils n (Ret x)) \<or> P = diverge"
  by (metis diverges_then_diverge is_Ret_def itree.collapse(3) itree.exhaust_disc stabilises_def)

lemma itree_cases:
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
    apply (metis itree.disc(7) itree.disc(8) itree.discI(3) itree.sel(3) no_divergence ranI stabilises_to.cases)
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

lemma no_divergence_Vis: "no_divergence (Vis F) = (ran F \<subseteq> Collect no_divergence)"
  apply (auto simp add: no_divergence)
  apply (smt (z3) domIff mem_Collect_eq option.sel option.simps(3) ran_def trace_to.intros(3))
  apply (metis no_divergence no_divergence_Sils stabilises_to_Sils_Vis stabilises_to_no_divergence)
  done

lemma no_divergence_stabilises_to: "no_divergence P \<Longrightarrow> stabilises_to no_divergence P"
  apply (cases P rule: itree_cases)
  apply (simp add: stabilises_alt_def' fun_eq_iff )
  apply (auto simp add: Sils_Vis_iff no_divergence_Sils no_divergence_Vis)
  done

lemma stabilises_to_is_no_diverge: "stabilises_to no_divergence = no_divergence"
  by (auto simp add: fun_eq_iff stabilises_to_no_divergence no_divergence_stabilises_to)

coinductive div_free :: "('e, 's) itree \<Rightarrow> bool" where
scons: "stabilises_to div_free P \<Longrightarrow> div_free P"

lemma div_free_Ret [simp]: "div_free (Ret x)"
  by (simp add: div_free.intros ret_stbs)

lemma div_free_Vis: "div_free (Vis F) \<longleftrightarrow> (\<forall> P \<in> ran F. div_free P)"
  by (metis (mono_tags, lifting) Ball_Collect Vis_Sils Vis_not_Sils_Ret div_free.simps stabilises_alt_def')

lemma div_free_Sil [simp]: "div_free (Sil P) = div_free P"
  by (metis div_free.simps is_Ret_def itree.disc(2) itree.disc(5) itree.disc(6) itree.sel(2) sil_stbs stabilises_to.cases)

lemma div_free_Sils: "div_free (Sils n P) \<longleftrightarrow> div_free P"
  by (induct n, auto)

lemma div_free_step: "\<lbrakk> P \<midarrow>[a]\<leadsto> P'; div_free P \<rbrakk> \<Longrightarrow> div_free P'"
  by (auto simp add: div_free_Vis div_free_Sils, meson div_free_Sils ranI)


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
  apply (meson div_free_Sils div_free_Vis ranI)
  done

lemma div_free_in_no_divergence: "div_free \<le> no_divergence"
  by (auto, metis div_free_diverge diverges_diverge diverges_implies_equal no_divergence trace_to_div_free)
  
lemma div_free_is_no_divergence: "div_free = no_divergence"
  by (simp add: antisym div_free_coind div_free_in_no_divergence predicate1I stabilises_to_is_no_diverge)

lemma div_free_no_min_divergence: "div_free P \<Longrightarrow> \<not> P \<midarrow>t\<leadsto> diverge"
  by (simp add: div_free_is_no_divergence no_divergence_def)

end