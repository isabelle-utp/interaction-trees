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

lemma dfp_event_choice [wp]: "dfp (event_choice F) = (pdom(F) \<noteq> {} \<and> (\<forall> e\<in>pdom(F). dfp(F(\<guillemotleft>e\<guillemotright>)\<^sub>p)\<^sub>e))\<^sub>e"
  by (simp add: dfp_def event_choice_def deadlock_free_Vis SEXP_def)

lemma dfp_event_block [wp]: "wb_prism c \<Longrightarrow> dfp (event_block c A (\<lambda> a. (P a, \<sigma> a))) = [\<lambda> s. \<exists> v\<in>A s. P v s]\<^sub>e"
  by (simp add: dfp_def event_block_def deadlock_free_Vis_prism_fun SEXP_def) 

(*
lemma case_sum_prod_dist: "case_sum (\<lambda> x. (f\<^sub>1 x, f\<^sub>2 x)) (\<lambda> x. (g\<^sub>1 x, g\<^sub>2 x)) = (\<lambda> x. (case_sum f\<^sub>1 g\<^sub>1 x, case_sum f\<^sub>2 g\<^sub>2 x))"
  by (simp add: fun_eq_iff sum.case_eq_if)

lemma case_sum_Ret_dist: "(case a of Inl x \<Rightarrow> Ret (f x) | Inr y \<Rightarrow> Ret (g y)) = Ret (case a of Inl x \<Rightarrow> f x | Inr y \<Rightarrow> g y)"
  by (simp add: sum.case_eq_if)
  
declare [[show_sorts]]

lemma "c \<nabla> d \<Longrightarrow> event_block c A PB \<box> event_block d B QB = event_block (c +\<^sub>\<triangle> d) (A <+> B)\<^sub>e undefined"

chantype chan =
  Input :: nat
  Output :: nat

definition "Num = {0::nat..9}"

find_theorems "(\<in>)" "(<+>)"

lemma Inl_in_Sum_iff [simp]: "Inl x \<in> A <+> B \<longleftrightarrow> x \<in> A"
  by fastforce

lemma Inr_in_Sum_iff [simp]: "Inr y \<in> A <+> B \<longleftrightarrow> y \<in> B"
  by fastforce

term "Bex"

lemma Bex_Sum_iff: "(\<exists>x\<in>A <+> B. P x) \<longleftrightarrow> (\<exists> x\<in>A. P (Inl x)) \<or> (\<exists> x\<in>B. P (Inr x))"
  by (auto)

lemma "deadlock_free (Vis (prism_fun Input Num (\<lambda> n. (True, Ret (buf @ [n]))) \<oplus> prism_fun Output Num (\<lambda> n. (length buf > 0 \<and> n = hd buf, Ret (tl buf)))))"
  apply (simp add: prism_fun_combine case_sum_prod_dist case_sum_Ret_dist deadlock_free_Vis_prism_fun Bex_Sum_iff)
  apply (auto simp add: Num_def)
  done

lemma "deadlock_free (Vis (prism_fun Output Num (\<lambda> n. (length buf > 0 \<and> n = hd buf, Ret (tl buf)))))"
  apply (simp add: prism_fun_combine case_sum_prod_dist case_sum_Ret_dist deadlock_free_Vis_prism_fun Bex_Sum_iff)
  nitpick
  apply (rule deadlock_free_Vis_prism_fun)
   apply (simp)
  apply (rule_tac x="Inl 0" in exI)
  apply simp

lemma "deadlock_free (Vis (prism_fun Input Num (\<lambda> n. (True, Ret (buf @ [n])))))"
  apply (rule deadlock_free_Vis_prism_fun)
   apply (simp)
  apply (auto simp add: Num_def)
*)

lemma deadlock_free_init_loop:
  assumes "\<sigma> establishes P" "C preserves P" "`P \<longrightarrow> dfp C`"
  shows "deadlock_free ((\<langle>\<sigma>\<rangle>\<^sub>a ;; loop C) s)"
  using assms
  apply (simp add: seq_itree_def kleisli_comp_def deadlock_free_bind_iff assigns_def dfp_def taut_def hoare_alt_def)
  apply (rule deadlock_free_loop[of P])
    apply (auto simp add: retvals_def)
  done

end