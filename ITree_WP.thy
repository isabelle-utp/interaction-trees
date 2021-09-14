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
  "_wlp S P" == "CONST wlp_itree S (P)\<^sub>e"

abbreviation "pre P \<equiv> wp P True"

expr_ctr pre

lemma wp_assigns [wp]: "wp \<langle>\<sigma>\<rangle>\<^sub>a P = (\<sigma> \<dagger> (P)\<^sub>e)"
  by (expr_simp add: wp_itree_def assigns_rel)

lemma wlp_assigns [wp]: "wlp \<langle>\<sigma>\<rangle>\<^sub>a P = (\<sigma> \<dagger> (P)\<^sub>e)"
  by (expr_simp add: wlp_itree_def assigns_rel)

lemma wp_assert [wp]: "wp (assert S) P = (S \<and> P)\<^sub>e"
  by (simp add: wp_itree_def assert_rel, expr_auto)

lemma wlp_assert [wp]: "wlp (assert S) P = (S \<longrightarrow> P)\<^sub>e"
  by (simp add: wlp_itree_def assert_rel, expr_simp)

lemma wp_test [wp]: "wp (test S) P = (S \<and> P)\<^sub>e"
  by (simp add: wp_itree_def test_rel, expr_simp)

lemma wlp_test [wp]: "wlp (test S) P = (S \<longrightarrow> P)\<^sub>e"
  by (simp add: wlp_itree_def test_rel, expr_simp)

lemma wp_seq [wp]: "wp (S \<Zcomp> R) P = wp S (wp R P)"
  by (auto simp add: wp_itree_def seq_rel)

lemma wlp_seq [wp]: "wlp (S \<Zcomp> R) P = wlp S (wlp R P)"
  by (auto simp add: wlp_itree_def seq_rel)

lemma wlp_true [wp]: "wlp P True = (True)\<^sub>e"
  by (expr_simp add: wlp_itree_def)

lemma wlp_Div [wp]: "wlp Div P = (True)\<^sub>e"
  by (simp add: wlp_itree_def Div_rel, expr_simp)

theorem hoare_via_wlp: "\<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>} = `P \<longrightarrow> wlp S Q`"
  by (simp add: hoare_triple_def spec_def wlp_itree_def, expr_auto)

method hoare_wlp = (simp add: hoare_via_wlp wp usubst_eval)
method hoare_wlp_auto = (hoare_wlp; expr_auto)

end