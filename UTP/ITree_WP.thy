section \<open> Weakest Preconditions \<close>

theory ITree_WP
  imports ITree_Hoare
begin

named_theorems wp

definition wp_itree :: "('e, 'a, 'b) ktree \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
"wp_itree S P = (\<lambda>s. \<exists> s'. (s, s') \<in> itree_rel S \<and> P s')"

definition wlp_itree :: "('e, 'a, 'b) ktree \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
"wlp_itree S P = (\<lambda>s. \<forall>s'. (s, s') \<in> itree_rel S \<longrightarrow> P s')"

expr_ctr wlp_itree wp_itree

syntax 
  "_wp"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("wp")
  "_wlp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("wlp")

translations
  "_wp S P" == "CONST wp_itree S (P)\<^sub>e"
  "_wp S" == "CONST wp_itree S"
  "_wlp S P" == "CONST wlp_itree S (P)\<^sub>e"
  "_wlp S" == "CONST wlp_itree S"

abbreviation "pre P \<equiv> wp P True"

expr_ctr pre

lemma wp_Skip [wp]: "wp Skip P = P"
  by (expr_simp add: wp_itree_def Skip_rel)

lemma wp_Skip' [wp]: "wp Skip = id"
  by (expr_simp add: wp_itree_def Skip_rel)

lemma wp_assigns [wp]: "wp \<langle>\<sigma>\<rangle>\<^sub>a P = (\<sigma> \<dagger> (P)\<^sub>e)"
  by (expr_simp add: wp_itree_def assigns_rel)

lemma wlp_assigns [wp]: "wlp \<langle>\<sigma>\<rangle>\<^sub>a P = (\<sigma> \<dagger> (P)\<^sub>e)"
  by (expr_simp add: wlp_itree_def assigns_rel)

lemma wp_assume [wp]: "wp (assume S) P = (S \<and> P)\<^sub>e"
  by (simp add: wp_itree_def assume_rel, expr_auto)

lemma wlp_assert [wp]: "wlp (assume S) P = (S \<longrightarrow> P)\<^sub>e"
  by (simp add: wlp_itree_def assume_rel, expr_simp)

lemma wp_test [wp]: "wp (test S) P = (S \<and> P)\<^sub>e"
  by (simp add: wp_itree_def test_rel, expr_simp)

lemma wlp_test [wp]: "wlp (test S) P = (S \<longrightarrow> P)\<^sub>e"
  by (simp add: wlp_itree_def test_rel, expr_simp)

lemma wp_seq [wp]: "wp (S \<Zcomp> R) P = wp S (wp R P)"
  by (auto simp add: wp_itree_def seq_rel)

lemma wp_seq': "wp (S \<Zcomp> R) = wp S \<circ> wp R"
  by (auto simp add: wp_itree_def seq_rel fun_eq_iff)

lemma wp_foldr_seq: "wp (foldr (\<lambda> i D. C i \<Zcomp> D) xs Skip) = foldr (\<lambda> i Q. wp (C i) \<circ> Q) xs id"
  by (induct xs, simp_all add: wp_Skip' wp_seq')

lemma wp_foldr_seq_term:
  assumes "\<And> x. pre (C x) = (True)\<^sub>e"
  shows "pre (foldr (\<lambda> i D. C i \<Zcomp> D) xs Skip) = (True)\<^sub>e"
  using assms by (induct xs, simp_all add: wp_Skip' wp_seq')

lemma wlp_seq [wp]: "wlp (S \<Zcomp> R) P = wlp S (wlp R P)"
  by (auto simp add: wlp_itree_def seq_rel)

lemma wlp_cond [wp]: "wlp (if B then C\<^sub>1 else C\<^sub>2 fi) P = ((B \<longrightarrow> wlp C\<^sub>1 P) \<and> (\<not> B \<longrightarrow> wlp C\<^sub>2 P))\<^sub>e"
  by (auto simp add: wlp_itree_def cond_rel fun_eq_iff)

lemma wlp_let [wp]: "wlp (let x \<leftarrow> e in S x) b = (wlp (S (e \<s>)) b)\<^sub>e"
  by (auto simp add: wlp_itree_def let_itree_def itree_rel_def retvals_def SEXP_def)

lemma wlp_true [wp]: "wlp P True = (True)\<^sub>e"
  by (expr_simp add: wlp_itree_def)

lemma wp_Div [wp]: "wp Div P = (False)\<^sub>e"
  by (simp add: wp_itree_def Div_rel, expr_simp)

lemma wlp_Div [wp]: "wlp Div P = (True)\<^sub>e"
  by (simp add: wlp_itree_def Div_rel, expr_simp)

lemma wp_Stop [wp]: "wp Stop P = (False)\<^sub>e"
  by (simp add: wp_itree_def Stop_rel, expr_simp)

lemma wlp_Stop [wp]: "wlp Stop P = (True)\<^sub>e"
  by (simp add: wlp_itree_def Stop_rel, expr_simp)

theorem hoare_via_wlp: "\<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>} = `P \<longrightarrow> wlp S Q`"
  by (simp add: hoare_triple_def spec_def wlp_itree_def, expr_auto)

method hoare_wlp = (simp add: hoare_via_wlp wp usubst_eval)
method hoare_wlp_auto = (hoare_wlp; expr_auto)

end