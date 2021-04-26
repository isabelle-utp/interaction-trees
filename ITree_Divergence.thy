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
  by (auto, auto simp add: Sils_Vis_iff stabilises_alt_def image_subset_iff, metis Sils_Vis_not_Ret)

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

coinductive div_free :: "('e, 's) itree \<Rightarrow> bool" where
scons: "stabilises_to div_free P \<Longrightarrow> div_free P"

find_theorems div_free

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

subsection \<open> Iteration \<close>

text \<open> For now we support only basic iteration for CSP processes. \<close>

corec while :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"while b P s = (if (b s) then (P s \<bind> (\<tau> \<circ> (while b P))) else Ret s)"

abbreviation "loop \<equiv> while (\<lambda> s. True)"

abbreviation "iter P \<equiv> loop (\<lambda> _. P) ()"

lemma loop_unfold: "loop P = P \<Zcomp> (\<tau> \<circ> loop P)"
  by (simp add: fun_eq_iff while.code)

lemma loop_Ret: "loop Ret = (\<lambda> s. diverge)"
  by (metis Sil_nfp_stabilises bind_Ret comp_apply diverges_then_diverge while.code)

end