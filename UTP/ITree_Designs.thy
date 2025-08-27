section \<open> Designs \<close>

theory ITree_Designs
  imports ITree_WP
begin

named_theorems dpre

text \<open> The design precondition captures the initial states that do not give the possibility of divergence. 
  This is different to the weakest precondition, which expresses the related property of the precondition
  under which the program terminates. \<close>

definition itree_pre :: "('e, 'r, 's) ktree \<Rightarrow> ('r \<Rightarrow> bool)" where
"itree_pre P = (\<lambda> s. \<not> (\<exists> es. P s \<midarrow>es\<leadsto> diverge))"

lemma itree_pre_div_free: "itree_pre P = (\<lambda> s. div_free (P s))"
  by (simp add: div_free_is_no_divergence itree_pre_def no_divergence_def)

expr_constructor itree_pre

definition refined_by :: "('e, 'r, 's) ktree \<Rightarrow> ('e, 'r, 's) ktree \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>\<D>" 50) where
"refined_by P Q = (`itree_pre P \<longrightarrow> itree_pre Q` \<and> {(s, s') \<in> itree_rel Q. itree_pre P s} \<subseteq> itree_rel P)"

lemma assume_pre [dpre]: "itree_pre (assume b) = b"
  by (auto simp add: itree_pre_def assume_def fun_eq_iff)

lemma assert_pre [dpre]: "itree_pre (assert b) = (True)\<^sub>e"
  by (auto simp add: itree_pre_def test_def fun_eq_iff)
     (metis deadlock_def deadlock_trace_to diverge_not_Vis)

lemma Skip_pre [dpre]: "itree_pre Skip = (True)\<^sub>e"
  by (auto simp add: itree_pre_def Skip_def)

lemma assigns_pre [dpre]: "itree_pre \<langle>\<sigma>\<rangle>\<^sub>a = (True)\<^sub>e"
  by (auto simp add: itree_pre_def assigns_def)

lemma Div_pre [dpre]: "itree_pre Div = (False)\<^sub>e"
  by (auto simp add: itree_pre_def fun_eq_iff)

lemma Div_bottom: "Div \<sqsubseteq>\<^sub>\<D> P"
  by (simp add: refined_by_def Div_rel Div_pre)

lemma Stop_pre [dpre]: "itree_pre Stop = (True)\<^sub>e"
  by (auto simp add: itree_pre_def fun_eq_iff deadlock_def)

lemma seq_pre [dpre]: "itree_pre (P ;; Q) = (itree_pre P \<and> wlp P (itree_pre Q))\<^sub>e"
  apply (expr_simp, auto elim!: trace_to_bindE simp add: kcomp_itree_def itree_pre_def wlp_itree_def itree_rel_defs retvals_def)
  apply (metis bind_diverge trace_to_bind_left)
  apply (meson trace_to_bind)
  apply (metis trace_of_Sils trace_to_Nil trace_to_trans)
  done

lemma cond_itree_pre [dpre]: "itree_pre (P \<lhd> b \<rhd> Q) = itree_pre P \<triangleleft> b \<triangleright> itree_pre Q"
  by (auto simp add: cond_itree_def itree_pre_def fun_eq_iff expr_if_def)

lemma input_in_pre [dpre]:
  "wb_prism c \<Longrightarrow> itree_pre (input_in c A P) = (\<forall> v \<in> A. itree_pre (P v))\<^sub>e"
  by (expr_simp add: itree_pre_div_free input_in_where_def div_free_bind div_free_inp_in retvals_inp_in)

method refine = (auto simp add: refined_by_def dpre wp usubst_eval unrest itree_rel relcomp_unfold)
method refine_auto = (refine ; expr_auto)

end