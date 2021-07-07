theory ITree_WP
  imports "ITree_Relation"
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

lemma wp_test [wp]: "wp \<questiondown>S? P = (S \<and> P)\<^sub>e"
  by (simp add: wp_itree_def test_rel, expr_simp)

lemma wp_seq [wp]: "wp (S \<Zcomp> R) P = wp S (wp R P)"
  by (auto simp add: wp_itree_def seq_rel)

lemma wlp_true [wp]: "wlp P True = (True)\<^sub>e"
  by (expr_simp add: wlp_itree_def)

lemma wlp_Div [wp]: "wlp Div P = (True)\<^sub>e"
  by (simp add: wlp_itree_def Div_rel, expr_simp)

end