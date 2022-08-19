section \<open> Deadlock Freedom Preconditions \<close>

theory ITree_DFP
  imports ITree_WP
begin

definition dfp :: "('e, 's, 'r) ktree \<Rightarrow> ('s \<Rightarrow> bool)" 
  where "dfp P = (\<lambda> s. deadlock_free (P s))"

expr_constructor dfp

lemma dfp_Stop [wp]: "dfp Stop = (False)\<^sub>e"
  by (simp add: dfp_def deadlock_free_deadlock SEXP_def)

lemma dfp_Skip [wp]: "dfp Skip = (True)\<^sub>e"
  by (simp add: dfp_def Skip_def deadlock_free_Ret SEXP_def)

lemma dfp_assigns [wp]: "dfp \<langle>\<sigma>\<rangle>\<^sub>a = (True)\<^sub>e"
  by (simp add: dfp_def assigns_def deadlock_free_Ret SEXP_def)

lemma dfp_seq [wp]: "dfp (P ;; Q) = (dfp P \<and> wlp P (dfp Q))\<^sub>e"
  by (simp add: dfp_def seq_itree_def kleisli_comp_def deadlock_free_bind_iff wlp_itree_def 
                SEXP_def retvals_def itree_rel_def itree_pred_def)

lemma deadlock_free_init_loop:
  assumes "\<sigma> establishes P" "C preserves P" "`P \<longrightarrow> dfp C`"
  shows "deadlock_free ((\<langle>\<sigma>\<rangle>\<^sub>a ;; loop C) s)"
  using assms
  apply (simp add: seq_itree_def kleisli_comp_def deadlock_free_bind_iff assigns_def dfp_def taut_def hoare_alt_def)
  apply (rule deadlock_free_loop[of P])
    apply (auto simp add: retvals_def)
  done

end