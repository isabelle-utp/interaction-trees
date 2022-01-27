section \<open> Countable Non-Determinism \<close>

theory ITree_Countable_Nondeterminism
  imports ITree_UTP
begin

text \<open> A type class to characterise a countable nondeterminism event. \<close>

class ndetev =
  fixes ndetev :: "nat \<Longrightarrow>\<^sub>\<triangle> 'a"
  assumes wb_ndetev [simp]: "wb_prism ndetev"

definition CNChoice :: "nat set \<Rightarrow> (nat \<Rightarrow> ('e::ndetev, 's) htree) \<Rightarrow> ('e, 's) htree" where
"CNChoice A P = input_in ndetev (\<lambda> _. A) P"

lemma CNChoice_pred [itree_pred]: "\<lbrakk>CNChoice A P\<rbrakk>\<^sub>p (s, s') = (\<exists>v\<in>A. \<lbrakk>P v\<rbrakk>\<^sub>p (s, s'))"
  by (simp add: CNChoice_def itree_pred)

chantype pndet =
  pndetev :: nat

instantiation pndet :: ndetev
begin
definition ndetev_pndet :: "nat \<Longrightarrow>\<^sub>\<triangle> pndet" where
"ndetev_pndet = pndetev"

instance by (intro_classes, simp add: ndetev_pndet_def)
end

definition prog_ndet :: "(pndet, 's) htree \<Rightarrow> (pndet, 's) htree \<Rightarrow> (pndet, 's) htree" where
"prog_ndet P Q = CNChoice {0, 1} ((\<lambda> x. Stop)(0 := P, 1 := Q))"

bundle prog_ndet_syntax
begin

notation
  prog_ndet (infixl "\<sqinter>" 60)

end

bundle no_prog_ndet_syntax
begin

no_notation
  prog_ndet (infixl "\<sqinter>" 60)

end

unbundle prog_ndet_syntax

lemma prog_ndet_pred [itree_pred]: "\<lbrakk>P \<sqinter> Q\<rbrakk>\<^sub>p (s, s') = ( \<lbrakk>P\<rbrakk>\<^sub>p (s, s') \<or> \<lbrakk>Q\<rbrakk>\<^sub>p (s, s'))"
  by (simp add: prog_ndet_def itree_pred)

lemma prog_ndet_rel [itree_rel]: "itree_rel (C\<^sub>1 \<sqinter> C\<^sub>2) = itree_rel C\<^sub>1 \<union> itree_rel C\<^sub>2"
  by (simp add: itree_rel_def itree_pred set_eq_iff)

lemma hl_prog_ndet [hoare_safe]:
  assumes "\<^bold>{P\<^bold>} C\<^sub>1 \<^bold>{Q\<^bold>}" "\<^bold>{P\<^bold>} C\<^sub>2 \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} C\<^sub>1 \<sqinter> C\<^sub>2 \<^bold>{Q\<^bold>}"
  using assms by (simp add: hoare_triple_def itree_rel)

lemma wp_prog_ndet [wp]: "wp (C\<^sub>1 \<sqinter> C\<^sub>2) P = (wp C\<^sub>1 P \<or> wp C\<^sub>2 P)\<^sub>e"
  by (expr_simp add: wp_itree_def itree_rel; auto)

lemma wlp_prog_ndet [wp]: "wlp (C\<^sub>1 \<sqinter> C\<^sub>2) P = (wlp C\<^sub>1 P \<and> wlp C\<^sub>2 P)\<^sub>e"
  by (expr_simp add: wlp_itree_def itree_rel; auto)

unbundle no_prog_ndet_syntax

end