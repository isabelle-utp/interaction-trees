section \<open> Deadlock Freedom Preconditions \<close>

theory ITree_DFP
  imports ITree_Hoare
begin

definition dfp :: "('e, 's, 'r) ktree \<Rightarrow> ('s \<Rightarrow> bool)" 
  where "dfp P = (\<lambda> s. deadlock_free (P s))"

expr_constructor dfp

lemma dfp_Stop [wp]: "dfp Stop = (False)\<^sub>e"
  by (simp add: dfp_def deadlock_free_deadlock SEXP_def)

lemma dfp_Skip [wp]: "dfp Skip = (True)\<^sub>e"
  by (simp add: dfp_def Skip_def deadlock_free_Ret SEXP_def)

lemma dfp_assume [wp]: "dfp (assume P) = (True)\<^sub>e"
  by (auto simp add: dfp_def assume_def deadlock_free_Ret deadlock_free_diverge)

lemma dfp_assert [wp]: "dfp (assert P) = (P)\<^sub>e"
  using deadlock_free_deadlock by (auto simp add: dfp_def test_def deadlock_free_Ret)

lemma dfp_assigns [wp]: "dfp \<langle>\<sigma>\<rangle>\<^sub>a = (True)\<^sub>e"
  by (simp add: dfp_def assigns_def deadlock_free_Ret SEXP_def)

lemma dfp_seq [wp]: "dfp (P ;; Q) = (dfp P \<and> wlp P (dfp Q))\<^sub>e"
  by (simp add: dfp_def seq_itree_def kleisli_comp_def deadlock_free_bind_iff wlp_itree_def 
                SEXP_def retvals_def itree_rel_def itree_pred_def)

lemma dfp_event_choice [wp]: "dfp (event_choice F) = (pdom(F) \<noteq> {} \<and> (\<forall> e\<in>pdom(F). dfp(F(\<guillemotleft>e\<guillemotright>)\<^sub>p)\<^sub>e))\<^sub>e"
  by (simp add: dfp_def event_choice_def deadlock_free_Vis SEXP_def)

lemma dfp_input_in_where [wp]: 
  assumes "wb_prism c"
  shows "dfp (input_in_where c A PC) = [\<lambda> s. (\<exists> v\<in>A s. fst (PC v) s) \<and> (\<forall> v\<in>A s. fst (PC v) s \<longrightarrow> dfp (snd (PC v)) s)]\<^sub>e"
  by (simp add: dfp_def input_in_where_prism_fun deadlock_free_Vis_prism_fun SEXP_def assms)

lemma dfp_output [wp]:
  assumes "wb_prism c"
  shows "dfp (c!(v) \<rightarrow> P) = dfp P"
  by (simp add: output_as_input wp assms, force)

lemma dfp_event_block [wp]: "wb_prism c \<Longrightarrow> dfp (event_block c A P\<sigma>) = [\<lambda> s. \<exists> v\<in>A s. fst (P\<sigma> v) s]\<^sub>e"
  by (simp add: dfp_def event_block_def deadlock_free_Vis_Ret_prism_fun SEXP_def) 

lemma deadlock_free_init_iterate:
  assumes "\<^bold>{True\<^bold>} \<langle>\<sigma>\<rangle>\<^sub>a \<^bold>{P\<^bold>}" "\<^bold>{P\<^bold>} C \<^bold>{P\<^bold>}" "`B \<and> P \<longrightarrow> dfp C`"
  shows "deadlock_free ((\<langle>\<sigma>\<rangle>\<^sub>a ;; iterate B C) s)"
  using assms
  apply (simp add: seq_itree_def kleisli_comp_def deadlock_free_bind_iff assigns_def dfp_def taut_def hoare_alt_def)
  apply (rule deadlock_free_iterate[of B P])
    apply (auto simp add: retvals_def)
  done

lemma deadlock_free_init_loop:
  assumes "\<^bold>{True\<^bold>} \<langle>\<sigma>\<rangle>\<^sub>a \<^bold>{P\<^bold>}" "\<^bold>{P\<^bold>} C \<^bold>{P\<^bold>}" "`P \<longrightarrow> dfp C`"
  shows "deadlock_free ((\<langle>\<sigma>\<rangle>\<^sub>a ;; loop C) s)"
  using assms
  by (auto intro: deadlock_free_init_iterate[of _ P])

end