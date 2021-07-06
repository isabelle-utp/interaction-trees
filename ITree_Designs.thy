theory ITree_Designs
  imports ITree_WP
begin

text \<open> The precondition captures the initial states that do not give the possibility of divergence. \<close>

definition itree_pre :: "('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool)" where
"itree_pre P = (\<lambda> s. \<not> (\<exists> es. P s \<midarrow>es\<leadsto> diverge))"

lemma itree_pre_div_free: "itree_pre P = (\<lambda> s. div_free (P s))"
  by (simp add: div_free_is_no_divergence itree_pre_def no_divergence_def)

expr_ctr itree_pre

definition refined_by :: "('e, 's) htree \<Rightarrow> ('e, 's) htree \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
"refined_by P Q = (`itree_pre P \<longrightarrow> itree_pre Q` \<and> {(s, s') \<in> itree_rel Q. itree_pre P s} \<subseteq> itree_rel P)"

lemma assigns_pre: "itree_pre \<langle>\<sigma>\<rangle>\<^sub>a = (True)\<^sub>e"
  by (auto simp add: itree_pre_def assigns_def)

lemma Div_pre: "itree_pre Div = (False)\<^sub>e"
  by (auto simp add: itree_pre_def fun_eq_iff)

lemma Div_bottom: "Div \<sqsubseteq> P"
  by (simp add: refined_by_def Div_rel Div_pre)

lemma Stop_pre: "itree_pre Stop = (True)\<^sub>e"
  by (auto simp add: itree_pre_def fun_eq_iff deadlock_def)

lemma seq_pre: "itree_pre (P \<Zcomp> Q) = (itree_pre P \<and> wlp P (itree_pre Q))\<^sub>e"
  apply (expr_simp, auto elim!: trace_to_bindE simp add: kleisli_comp_def itree_pre_def wlp_itree_def itree_rel_def retvals_def)
  apply (metis bind_diverge trace_to_bind_left)
  apply (meson trace_to_bind)
  apply (metis trace_of_Sils trace_to_Nil trace_to_trans)
  done

lemma input_in_pre:
  "wb_prism c \<Longrightarrow> itree_pre (input_in c A P) = (\<forall> v \<in> A. itree_pre (P v))\<^sub>e"
  by (expr_simp add: itree_pre_div_free input_in_def div_free_bind div_free_inp_in retvals_inp_in)

end