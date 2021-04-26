section \<open> Weak Bisimulation \<close>

theory ITree_Weak_Bisim
  imports ITree_Divergence
begin

text \<open> See Hennessy's paper relating CCS and CSP. If you forget divergence, i+1 equivalence and 
  its limit. 2.5 equivalence. "ON THE RELATIONSHIP OF CCS AND CSP". \<close>

inductive wbisim_to :: "('e, 's) itree \<Rightarrow> (('e, 's) itree \<Rightarrow> ('e, 's) itree \<Rightarrow> bool) \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" (infix "\<approx>\<^bsub>_\<^esub>" 50) where
wbisim_to_Ret [intro]: "Ret x \<approx>\<^bsub>\<R>\<^esub> Ret x" |
wbisim_to_Sil1 [intro]: "P \<approx>\<^bsub>\<R>\<^esub> Q \<Longrightarrow> Sil P \<approx>\<^bsub>\<R>\<^esub> Q" |
wbisim_to_Sil2 [intro]: "P \<approx>\<^bsub>\<R>\<^esub> Q \<Longrightarrow> P \<approx>\<^bsub>\<R>\<^esub> Sil Q" |
wbisim_to_Vis [intro]: "\<lbrakk> pdom(F) = pdom(G); \<And> e. e \<in> pdom(F) \<Longrightarrow> \<R> (F e) (G e) \<rbrakk> \<Longrightarrow> Vis F \<approx>\<^bsub>\<R>\<^esub> Vis G"

inductive_cases
  wbisim_RetE [elim]: "Ret x \<approx>\<^bsub>\<R>\<^esub> P" and
  wbisim_SilE [elim]: "Sil P \<approx>\<^bsub>\<R>\<^esub> Q"

thm wbisim_SilE

lemma monotonic_wbisim_to: "P \<approx>\<^bsub>\<R>\<^sub>1\<^esub> Q \<Longrightarrow> \<R>\<^sub>1 \<le> \<R>\<^sub>2 \<Longrightarrow> P \<approx>\<^bsub>\<R>\<^sub>2\<^esub> Q"
  by (induct rule: wbisim_to.induct, auto)

lemma mono_wbisim_to [mono add]: "\<R>\<^sub>1 \<le> \<R>\<^sub>2 \<Longrightarrow> (\<lambda> P Q. P \<approx>\<^bsub>\<R>\<^sub>1\<^esub> Q) \<le> (\<lambda> P Q. P \<approx>\<^bsub>\<R>\<^sub>2\<^esub> Q)"
  using monotonic_wbisim_to by auto

lemma wbisim_to_Sils1 [intro]: "P \<approx>\<^bsub>\<R>\<^esub> Q \<Longrightarrow> Sils n P \<approx>\<^bsub>\<R>\<^esub> Q"
  by (induct n, auto)

lemma wbisim_to_Sils2 [intro]: "P \<approx>\<^bsub>\<R>\<^esub> Q \<Longrightarrow> P \<approx>\<^bsub>\<R>\<^esub> Sils n Q"
  by (induct n, auto)

lemma wbisim_toD:
  "P \<approx>\<^bsub>\<R>\<^esub> Q \<Longrightarrow>
  ((\<exists> m n x. P = Sils m (Ret x) \<and> Q = Sils n (Ret x)) 
   \<or> (\<exists> m n F G. P = Sils m (Vis F) \<and> Q = Sils n (Vis G) \<and> pdom(F) = pdom(G) \<and> (\<forall> e \<in> pdom(F). \<R> (F e) (G e))))"
  by (induct rule: wbisim_to.induct, auto, (metis (full_types) Sils.simps(1) Sils.simps(2))+)[1]

lemma wbisim_toE [elim]:
  assumes "P \<approx>\<^bsub>\<R>\<^esub> Q"
  "\<And> m n x. \<lbrakk> P = Sils m (Ret x); Q = Sils n (Ret x) \<rbrakk> \<Longrightarrow> R"
  "\<And> m n F G. \<lbrakk> P = Sils m (Vis F); Q = Sils n (Vis G); pdom(F) = pdom(G); (\<forall> e \<in> pdom(F). \<R> (F e) (G e)) \<rbrakk> \<Longrightarrow> R"
  shows R 
  using assms by (auto dest: wbisim_toD)
  
lemma wbisim_to_SilD1: "(\<tau> P \<approx>\<^bsub>\<R>\<^esub> Q) \<Longrightarrow> (P \<approx>\<^bsub>\<R>\<^esub> Q)"
  apply (erule wbisim_toE)
  apply (auto)
  apply (metis (no_types, lifting) Sils.elims itree.distinct(1) itree.sel(2) wbisim_to_Ret wbisim_to_Sils1 wbisim_to_Sils2)
  apply (metis (no_types, hide_lams) itree.disc(8) itree.disc(9) wbisim_SilE wbisim_to_Sils1 wbisim_to_Sils2 wbisim_to_Vis)
  done

lemma wbisim_to_Sil_iff1 [simp]: "(\<tau> P \<approx>\<^bsub>\<R>\<^esub> Q) \<longleftrightarrow> (P \<approx>\<^bsub>\<R>\<^esub> Q)"
  by (metis wbisim_to_Sil1 wbisim_to_SilD1)

lemma wbisim_to_Sils_iff1 [simp]: "(Sils n P \<approx>\<^bsub>\<R>\<^esub> Q) \<longleftrightarrow> (P \<approx>\<^bsub>\<R>\<^esub> Q)"
  by (induct n, auto)

lemma wbisim_to_SilD2: "(P \<approx>\<^bsub>\<R>\<^esub> \<tau> Q) \<Longrightarrow> (P \<approx>\<^bsub>\<R>\<^esub> Q)"
  apply (erule wbisim_toE)
  apply (auto)
  apply (metis (no_types, lifting) Sils.elims itree.distinct(1) itree.sel(2) wbisim_to_Ret wbisim_to_Sils1 wbisim_to_Sils2)
  apply (metis (no_types, lifting) Sils.elims itree.disc(8) itree.disc(9) itree.sel(2) wbisim_to_Sils1 wbisim_to_Sils2 wbisim_to_Vis)
  done

lemma wbisim_to_Sil_iff2 [simp]: "(P \<approx>\<^bsub>\<R>\<^esub> \<tau> Q) \<longleftrightarrow> (P \<approx>\<^bsub>\<R>\<^esub> Q)"
  by (metis wbisim_to_Sil2 wbisim_to_SilD2)

lemma wbisim_to_Sils_iff2 [simp]: "(P \<approx>\<^bsub>\<R>\<^esub> Sils n Q) \<longleftrightarrow> (P \<approx>\<^bsub>\<R>\<^esub> Q)"
  by (induct n, auto)

lemma wbisim_to_ndiv1 [elim]: "diverge \<approx>\<^bsub>\<R>\<^esub> P \<Longrightarrow> False"
  apply (erule wbisim_toE)
  apply (metis div_free_Ret div_free_Sils div_free_diverge)
  apply (metis (no_types, hide_lams) Sils_diverge Sils_injective diverge_not_Vis)
  done

lemma wbisim_to_ndiv2 [elim]: "P \<approx>\<^bsub>\<R>\<^esub> diverge \<Longrightarrow> False"
  apply (erule wbisim_toE)
  apply (metis div_free_Ret div_free_Sils div_free_diverge)
  apply (metis (no_types, hide_lams) Sils_diverge Sils_injective diverge_not_Vis)
  done

coinductive wbisim :: "('e, 's) itree \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" (infix "\<approx>" 50) where
wbisim_divI: "diverge \<approx> diverge" |
wbisimI: "P \<approx>\<^bsub>(\<approx>)\<^esub> Q \<Longrightarrow> P \<approx> Q"

lemma wbisim_set_rep: 
  "(\<approx>) = (\<lambda> x y. (x, y) \<in> \<Union> {\<R>. \<R> \<subseteq> {(P, Q). P = diverge \<and> Q = diverge \<or> (P \<approx>\<^bsub>(\<lambda> x y. (x, y) \<in> \<R>)\<^esub> Q)}})"
  apply (simp add: fun_eq_iff)
  apply (safe)
   apply (rule_tac x="{(x, y). x \<approx> y}" in exI)
  apply (auto)[1]
  apply (metis wbisim.cases)
  apply (metis wbisim.cases)
  apply (subst HOL.nitpick_unfold(192))
  apply (simp add: gfp_def)
  apply (smt (z3) BNF_Def.Collect_case_prodD basic_trans_rules(31) predicate2I prod.sel(1) prod.sel(2))
  done
  
lemma diverge_wbisim1: "diverge \<approx> Q \<Longrightarrow> Q = diverge"
  apply (coinduction rule: itree_strong_coind)
  apply (metis diverge.disc_iff wbisim.cases wbisim_to_ndiv1)
  apply (metis diverge_not_Ret)
  apply (metis itree.inject(2) wbisim.cases wbisim_to_ndiv1)
  apply (metis diverge_not_Vis)
  done

lemma diverge_wbisim2: "P \<approx> diverge \<Longrightarrow> P = diverge"
  apply (coinduction rule: itree_strong_coind)
  apply (metis (no_types, lifting) wbisim.cases wbisim_to_ndiv2)
  apply (metis diverge_not_Ret)
  apply (metis itree.inject(2) wbisim.cases wbisim_to_ndiv2)
  apply (metis diverge_not_Vis)
  done

lemma wbisim_refl [intro]: "P \<approx> P"
proof (cases "divergent P")
  case True
  then show ?thesis
    by (metis (mono_tags, hide_lams) diverges_then_diverge wbisim_divI) 
next
  case False
  then show ?thesis
    apply (auto)
    apply (coinduction arbitrary: P)
    apply (auto)
    apply (smt (verit, best) diverges_diverge diverges_implies_equal itree.collapse(1) itree.collapse(3) itree.exhaust_disc stabilises_def wbisim_divI wbisim_to.intros(1) wbisim_to_Sils1 wbisim_to_Sils2 wbisim_to_Vis)
    done
qed

lemma wbisim_sym [intro]: "P \<approx> Q \<Longrightarrow> Q \<approx> P"
  apply (case_tac "P = diverge")
  apply (simp)
   apply (metis (no_types, hide_lams) diverge_wbisim1)
  apply (case_tac "Q = diverge")
   apply (simp)
   apply (metis (no_types, hide_lams) diverge_wbisim2)
  apply (coinduction arbitrary: P Q)
  apply (auto elim!: wbisim.cases wbisim_toE intro!: wbisim_to_Sils1 wbisim_to_Sils2 wbisim_to_Vis)
  apply (metis diverge_wbisim1)
  apply (metis diverge_wbisim2)
  done

lemma wbisim_SilI1 [intro]: "P \<approx> Q \<Longrightarrow> \<tau> P \<approx> Q"
  by (metis diverge.code wbisim.cases wbisimI wbisim_to_Sil1)

lemma wbisim_SilI2 [intro]: "P \<approx> Q \<Longrightarrow> P \<approx> \<tau> Q"
  by (metis (no_types, hide_lams) wbisim_SilI1 wbisim_sym)

lemma Sil_wbisim_iff1 [simp]: "\<tau> P \<approx> Q \<longleftrightarrow> P \<approx> Q"
proof 
  show "P \<approx> Q \<Longrightarrow> \<tau> P \<approx> Q" by auto
next
  assume \<tau>: "\<tau> P \<approx> Q"
  show "P \<approx> Q"
  proof (cases "divergent P")
    case True
    with \<tau> show ?thesis
      by (metis (no_types, hide_lams) diverge.code diverges_then_diverge)
  next
    case False
    with \<tau> have stb: "stabilises Q"
      by (metis (no_types, hide_lams) diverge_wbisim2 diverges_then_diverge stabilises_Sil)
    with \<tau> show ?thesis
      by (metis diverges_then_diverge wbisim.simps wbisim_to_SilD1)
  qed
qed

lemma Sil_wbisim_iff2 [simp]: "P \<approx> \<tau> Q \<longleftrightarrow> P \<approx> Q"
  by (metis Sil_wbisim_iff1 wbisim_sym)

lemma wbisim_Sils_iff1 [simp]: "Sils n P \<approx> Q \<longleftrightarrow> P \<approx> Q"
  by (metis Sils_diverge Sils_injective wbisim.simps wbisim_to_Sils_iff1)

lemma wbisim_Sils_iff2 [simp]: "P \<approx> Sils n Q \<longleftrightarrow> P \<approx> Q"
  by (metis (mono_tags, hide_lams) wbisim_Sils_iff1 wbisim_sym)

lemma wbisim_Sils [intro]: "P \<approx> Q \<Longrightarrow> Sils n P \<approx> Q"
  by (induct n, auto)

lemma wbisim_bothVisI [intro]: "\<lbrakk> pdom(F) = pdom(G); \<And> e. e \<in> pdom(F) \<Longrightarrow> (F e) \<approx> (G e) \<rbrakk> \<Longrightarrow> Vis F \<approx> Vis G"
  by (rule wbisimI, force)

lemma wbisim_both_VisE [elim]: "\<lbrakk> Vis F \<approx> Vis G; \<lbrakk> pdom(F) = pdom(G); \<And> e. e \<in> pdom(F) \<Longrightarrow> (F e) \<approx> (G e) \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto elim: wbisim.cases wbisim_to.cases)

lemma wbisim_Vis_eq:
  "\<lbrakk> Vis F \<approx> Q \<rbrakk> \<Longrightarrow> \<exists> n G. Q = Sils n (Vis G) \<and> pdom(F) = pdom(G) \<and> (\<forall> e \<in> pdom(F). (F e) \<approx> (G e))"
  by (auto elim!: wbisim.cases)
     (smt (verit, best) Vis_not_Sils_Ret wbisimI wbisim_Sils_iff2 wbisim_both_VisE wbisim_toD)

lemma wbisim_VisE:
  assumes "Vis F \<approx> Q" "\<And> n G. \<lbrakk> Q = Sils n (Vis G); pdom(F) = pdom(G); \<And> e. e \<in> pdom(F) \<Longrightarrow> (F e) \<approx> (G e) \<rbrakk> \<Longrightarrow> R"
  shows R
  by (metis (mono_tags, lifting) assms(1) assms(2) wbisim_Vis_eq)
  
lemma wbisim_trans: 
  assumes "P \<approx> Q" "Q \<approx> R" 
  shows "P \<approx> R"
proof (cases "divergent P")
  case True
  then show ?thesis
    by (metis assms(1) assms(2) diverges_then_diverge wbisim.cases wbisim_to_ndiv1) 
next
  case False
  with assms have stbs: "stabilises P" "stabilises Q" "stabilises R"
    apply (metis (no_types, hide_lams))
    apply (metis (mono_tags, lifting) False assms(1) diverge_wbisim2 diverges_then_diverge)
    apply (metis (mono_tags, lifting) False assms(1) assms(2) diverge_wbisim2 diverges_then_diverge)
    done
  with assms show ?thesis 
    apply (coinduction arbitrary: P Q R)
    apply (auto elim!: wbisim.cases wbisim_toE intro!: wbisim_to_Sils1 wbisim_to_Sils2 wbisim_to_Vis)
    apply (metis (no_types, lifting) termination_determinsitic trace_of_Sils wbisim_to_Ret)
    apply (metis (no_types, lifting) wbisim_to_Ret wbisim_to_Sils_iff2)
    apply (metis (no_types, lifting) Sils_Vis_not_Ret)
    apply (metis (no_types, lifting) Sils_Vis_not_Ret)
    apply (metis (no_types, lifting) Sils_Vis_not_Ret)
    apply (metis (no_types, lifting) Sils_Vis_not_Ret)
    apply (metis (no_types, hide_lams) Sils_Vis_iff)
    apply (metis (no_types, hide_lams) Sils_Vis_inj)
    apply (metis (no_types, hide_lams) Sils_Vis_iff)
    apply (metis (no_types, hide_lams) Sils_Vis_iff)
    apply (metis (no_types, hide_lams) Sils_Vis_inj diverge_wbisim1 diverge_wbisim2 diverges_then_diverge)
    apply (metis Sils_Vis_inj diverge_wbisim1 diverge_wbisim2 diverges_then_diverge)
    done
qed

lemma wbisim_coind: 
  assumes 
    "\<R> P Q"
    "\<And> P Q. \<R> P Q \<Longrightarrow> \<R> Q P"
    "\<And> P. \<R> diverge P \<Longrightarrow> P = diverge"
    "\<And> n P Q. \<R> (Sils n P) Q \<Longrightarrow> \<R> P Q"
    "\<And> P Q. \<lbrakk> \<R> P Q; stable P; stable Q \<rbrakk> \<Longrightarrow> (is_Vis P \<longleftrightarrow> is_Vis Q) \<and> (is_Ret P \<longleftrightarrow> is_Ret Q)"
    "\<And> F G. \<R> (Vis F) (Vis G) \<Longrightarrow> pdom F = pdom G \<and> (\<forall> e \<in> pdom(F). \<R> (F e) (G e))"
    "\<And> x y. \<R> (Ret x) (Ret y) \<Longrightarrow> x = y"
  shows "P \<approx> Q"
proof (rule wbisim.coinduct[of \<R>, OF assms(1)], simp)
  fix P Q
  assume PQ: "\<R> P Q"
  show "P = diverge \<and> Q = diverge \<or> P \<approx>\<^bsub>(\<lambda> x y. \<R> x y \<or> x \<approx> y)\<^esub> Q"
  proof (cases "divergent P")
  case True    
  then show ?thesis
    by (metis PQ assms(3) diverges_then_diverge)
  next
    case False
    hence ndiv: "P \<noteq> diverge \<and> Q \<noteq> diverge"
      by (metis (no_types, lifting) PQ assms(2) assms(3) diverges_then_diverge)
    have "P \<approx>\<^bsub>(\<lambda>x y. \<R> x y \<or> x \<approx> y)\<^esub> Q"
    proof (cases P rule: itree_cases)
      case (Vis m F)
      hence R1: "\<R> (Vis F) Q"
        by (metis PQ assms(4))
      obtain n Q' where Q: "Q = Sils n Q'" "stable Q'"
        by (metis diverges_then_diverge ndiv stabilises_def)
      hence "\<R> (Vis F) Q'"
        by (metis (no_types, lifting) R1 assms(2) assms(4))
      then obtain G where Q': "Q' = Vis G"
        by (metis (no_types, lifting) \<open>stable Q'\<close> assms(5) is_VisE itree.disc(9) stable_Vis)
      have "pdom(F) = pdom(G)"
        by (metis (mono_tags, lifting) \<open>Q' = Vis G\<close> \<open>\<R> (Vis F) Q'\<close> assms(6))
      moreover have "(\<forall> e \<in> pdom(F). \<R> (F e) (G e))"
        by (metis (no_types, lifting) Q' \<open>\<R> (Vis F) Q'\<close> assms(6))
      ultimately have "P \<approx>\<^bsub>\<R>\<^esub> Q"
        by (metis Q' Q(1) Vis wbisim_to_Sils1 wbisim_to_Sils2 wbisim_to_Vis)
      thus ?thesis
        by (metis (mono_tags, lifting) monotonic_wbisim_to predicate2I)
    next
      case (Ret m x)
      then obtain n y where "Q = Sils n (Ret y)"
        by (metis (no_types, hide_lams) PQ assms(2) assms(4) assms(5) itree.disc(4) itree.disc(7) itree.disc(9) itree.distinct_disc(6) itree_disj_cases ndiv)
      with Ret show ?thesis
        by (metis (no_types, lifting) PQ assms(2) assms(4) assms(7) wbisim_to_Ret wbisim_to_Sils1 wbisim_to_Sils2)
    next
      case diverge
      then show ?thesis
        by (metis ndiv)
    qed
    thus ?thesis
      by metis
  qed
qed

lemma wbisim_strong_coind: 
  assumes 
    "\<R> P Q"
    "\<And> P Q. \<R> P Q \<Longrightarrow> \<R> Q P"
    "\<And> P. \<R> diverge P \<Longrightarrow> P = diverge"
    "\<And> n P Q. \<R> (Sils n P) Q \<Longrightarrow> \<R> P Q \<or> P \<approx> Q"
    "\<And> P Q. \<lbrakk> \<R> P Q; stable P; stable Q \<rbrakk> \<Longrightarrow> (is_Vis P \<longleftrightarrow> is_Vis Q) \<and> (is_Ret P \<longleftrightarrow> is_Ret Q)"
    "\<And> F G. \<R> (Vis F) (Vis G) \<Longrightarrow> pdom F = pdom G \<and> (\<forall> e \<in> pdom(F). \<R> (F e) (G e) \<or> (F e) \<approx> (G e))"
    "\<And> x y. \<R> (Ret x) (Ret y) \<Longrightarrow> x = y"
  shows "P \<approx> Q"
  apply (rule wbisim_coind[of "\<lambda> x y. \<R> x y \<or> x \<approx> y"])
  apply (simp_all add: assms)
  apply (metis (mono_tags, lifting) assms(2) wbisim_sym)
  apply (metis (full_types) assms(3) diverge_wbisim1)
  apply (metis (mono_tags, lifting) assms(4))
  apply (metis (no_types, lifting) assms(5) itree.case_eq_if itree.disc(5) itree.disc(9) itree.disc_eq_case(3) wbisim.cases wbisim_to.simps)
  apply (metis assms(6) wbisim_both_VisE)
  apply (metis (no_types, lifting) assms(7) itree.distinct(1) itree.inject(1) wbisim.cases wbisim_RetE)
  done

lemma wbisim_trace_to_Nil: "P \<midarrow>[]\<leadsto> P' \<Longrightarrow> P \<approx> P'"
  by auto

lemma wbisim_step_rule: 
  assumes 
    "\<forall> tr P'. P \<midarrow>tr\<leadsto> P' \<longrightarrow> (\<exists> Q'. Q \<midarrow>tr\<leadsto> Q' \<and> P' \<approx> Q')"
    "\<forall> tr Q'. Q \<midarrow>tr\<leadsto> Q' \<longrightarrow> (\<exists> P'. P \<midarrow>tr\<leadsto> P' \<and> P' \<approx> Q')"
  shows "P \<approx> Q"
  by (metis (mono_tags, lifting) assms(1) trace_to_Nil wbisim_sym wbisim_trace_to_Nil wbisim_trans)

lemma wbsim_silent_step: "\<lbrakk> P \<approx> Q; P \<midarrow>[]\<leadsto> P' \<rbrakk> \<Longrightarrow> \<exists> Q'. Q \<midarrow>[]\<leadsto> Q' \<and> P' \<approx> Q'"
  by (metis (mono_tags, lifting) trace_to_Nil wbisim_sym wbisim_trace_to_Nil wbisim_trans)

lemma wbisim_single_step: "\<lbrakk> P \<approx> Q; P \<midarrow>[e]\<leadsto> P' \<rbrakk> \<Longrightarrow> \<exists> Q'. Q \<midarrow>[e]\<leadsto> Q' \<and> P' \<approx> Q'"
  apply (erule trace_to_singleE)
  apply (auto elim!: trace_to_singleE wbisim_VisE)
  apply (metis (no_types, lifting) trace_of_Sils wbsim_silent_step)
  done

lemma wbisim_step: "\<lbrakk> P \<approx> Q; P \<midarrow>tr\<leadsto> P' \<rbrakk> \<Longrightarrow> \<exists> Q'. Q \<midarrow>tr\<leadsto> Q' \<and> P' \<approx> Q'"
  apply (induct tr arbitrary: P Q P')
   apply (metis wbsim_silent_step)
  apply (erule trace_to_ConsE)
  apply (erule trace_to_ConsE)
  apply (auto elim!: wbisim_VisE)
  apply (metis (no_types, hide_lams) trace_to_NilE wbisim_Sils_iff1)
  done

lemma wbisim_silent_step_terminate: "\<lbrakk> P \<approx> Q; P \<midarrow>[]\<leadsto> Ret x \<rbrakk> \<Longrightarrow> Q \<midarrow>[]\<leadsto> Ret x"
  by (auto elim!: wbisim.cases)
     (smt (verit, best) Sils_Vis_not_Ret Sils_to_Ret trace_to_Nil_Sils wbisim_toD)

lemma wbisim_single_step_terminate: "\<lbrakk> P \<approx> Q; P \<midarrow>[e]\<leadsto> Ret x \<rbrakk> \<Longrightarrow> Q \<midarrow>[e]\<leadsto> Ret x"
  apply (erule trace_to_singleE)
  apply (auto elim!: trace_to_singleE wbisim_VisE)
  apply (metis (no_types, hide_lams) Sils_Vis_not_Ret termination_determinsitic trace_of_Sils wbisim.cases wbisim_toD)
  done

lemma wbisim_step_terminate: "\<lbrakk> P \<approx> Q; P \<midarrow>tr\<leadsto> Ret x \<rbrakk> \<Longrightarrow> Q \<midarrow>tr\<leadsto> Ret x"
  apply (induct tr arbitrary: P Q)
  apply (metis (mono_tags, hide_lams) wbisim_silent_step_terminate)
  apply (smt (verit, ccfv_SIG) trace_to_Cons trace_to_ConsE wbisim_step)
  done

lemma wbisim_silent_step_stable: "\<lbrakk> P \<approx> Q; P \<midarrow>[]\<leadsto> P'; stable P' \<rbrakk> \<Longrightarrow> \<exists> Q'. Q \<midarrow>[]\<leadsto> Q' \<and> stable Q' \<and> P' \<approx> Q'"
  by (metis (no_types, hide_lams) diverges_then_diverge stabilises_def trace_of_Sils wbisim.cases wbisim_sym wbisim_to_ndiv2 wbisim_trace_to_Nil wbisim_trans)
 
lemma wbisim_single_step_stable: 
  assumes "P \<approx> Q" "P \<midarrow>[e]\<leadsto> P'" "stable P'"
  shows "\<exists> Q'. Q \<midarrow>[e]\<leadsto> Q' \<and> stable Q' \<and> P' \<approx> Q'"
proof -
  obtain Q\<^sub>0 where Q\<^sub>0: "Q \<midarrow>[e]\<leadsto> Q\<^sub>0" "P' \<approx> Q\<^sub>0"
    by (metis (no_types, lifting) assms(1) assms(2) wbisim_single_step)
  hence "stabilises Q\<^sub>0"
    by (metis assms(3) diverges_implies_unstable diverges_then_diverge wbisim.cases wbisim_to_ndiv2)
  then obtain Q' n where Q': "Q\<^sub>0 = Sils n Q'" "stable Q'"
    by (metis stabilises_def)
  hence "Q \<midarrow>[e]\<leadsto> Q'" "P' \<approx> Q'"
    by (metis Q\<^sub>0(1) trace_of_Sils trace_to_Cons)
       (metis Q'(1) Q\<^sub>0(2) wbisim_Sils_iff2)
  thus ?thesis
    by (metis (full_types) Q'(2))
qed

lemma wbisim_step_stable:
  assumes "P \<approx> Q" "P \<midarrow>tr\<leadsto> P'" "stable P'"
  shows "\<exists> Q'. Q \<midarrow>tr\<leadsto> Q' \<and> stable Q' \<and> P' \<approx> Q'"
  using assms
  apply (induct tr arbitrary: P Q P')
   apply (metis (full_types) wbisim_silent_step_stable)
  apply (erule trace_to_ConsE)
  apply (auto elim!: wbisim_VisE)
  apply (metis wbisim_Sils_iff1)
  done

lemma "(\<And>s. Q\<^sub>1 s \<approx> Q\<^sub>2 s) \<Longrightarrow> P \<bind> Q\<^sub>1 \<approx> P \<bind> Q\<^sub>2"
  apply (rule wbisim_strong_coind[of "\<lambda> x y. \<exists> P Q. x = P \<bind> Q\<^sub>1 \<and> y = P \<bind> Q\<^sub>2 \<or> y = P \<bind> Q\<^sub>1 \<and> x = P \<bind> Q\<^sub>2"])
  oops

  
text \<open> For CCS, weak bisimulation is not a congruence with respect to choice. Hence, Milner creates
  a derived relation, observation congruence, which adds the requirement that an initial silent
  action must be matched by a silent action in the other process. This is an issue because $\tau$
  can resolve a choice in CCS. \<close>

end