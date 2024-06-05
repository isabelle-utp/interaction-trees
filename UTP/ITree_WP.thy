section \<open> Weakest Preconditions \<close>

theory ITree_WP
  imports ITree_Relation
begin

named_theorems wp

definition wp_itree :: "('e, 'a, 'b) ktree \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
"wp_itree S P = (\<lambda>s. \<exists> s'. (s, s') \<in> itree_rel S \<and> P s')"

definition wlp_itree :: "('e, 'a, 'b) ktree \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
"wlp_itree S P = (\<lambda>s. \<forall>s'. (s, s') \<in> itree_rel S \<longrightarrow> P s')"

expr_constructor wlp_itree wp_itree

syntax 
  "_wp"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("wp")
  "_wlp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("wlp")

translations
  "_wp S P" == "CONST wp_itree S (P)\<^sub>e"
  "_wp S" == "CONST wp_itree S"
  "_wlp S P" == "CONST wlp_itree S (P)\<^sub>e"
  "_wlp S" == "CONST wlp_itree S"

lemma wlp_alt_def: "wlp S P = (\<lambda> s. \<forall> tr s'. S(s) \<midarrow>tr\<leadsto> \<checkmark> s' \<longrightarrow> P s')"
  by (auto simp add: wlp_itree_def itree_rel_def itree_pred_def retvals_def fun_eq_iff)

lemma wp_alt_def: "wp S P = (\<lambda> s. \<exists> tr s'. S(s) \<midarrow>tr\<leadsto> \<checkmark> s' \<and> P s')"
  by (auto simp add: wp_itree_def itree_rel_def itree_pred_def retvals_def fun_eq_iff)

abbreviation "pre P \<equiv> wp P True"

text \<open> The precondition corresponds to termination \<close>

lemma pre_terminates: "pre P = (terminates P)\<^sub>e"
  unfolding wp_alt_def by (auto simp add: SEXP_def terminates_def)

expr_constructor pre

lemma wp_Skip [wp]: "wp Skip P = P"
  by (expr_simp add: wp_itree_def Skip_rel)

lemma wlp_Skip [wp]: "wlp Skip P = P"
  by (expr_simp add: wlp_itree_def Skip_rel)

lemma wp_Skip' [wp]: "wp Skip = id"
  by (expr_simp add: wp_itree_def Skip_rel)

lemma wp_assigns [wp]: "wp \<langle>\<sigma>\<rangle>\<^sub>a P = (\<sigma> \<dagger> (P)\<^sub>e)"
  by (expr_simp add: wp_itree_def assigns_rel)

lemma wlp_assigns [wp]: "wlp \<langle>\<sigma>\<rangle>\<^sub>a P = (\<sigma> \<dagger> (P)\<^sub>e)"
  by (expr_simp add: wlp_itree_def assigns_rel)

lemma wlp_assign: "wlp (x := e) P = (P)\<^sub>e\<lbrakk>e/x\<rbrakk>"
  by (simp add: wlp_assigns)

lemma wp_assume [wp]: "wp (assume S) P = (S \<and> P)\<^sub>e"
  by (simp add: wp_itree_def assume_rel, expr_auto)

lemma wlp_assert [wp]: "wlp (assume S) P = (S \<longrightarrow> P)\<^sub>e"
  by (simp add: wlp_itree_def assume_rel, expr_simp)

lemma wp_test [wp]: "wp (test S) P = (S \<and> P)\<^sub>e"
  by (simp add: wp_itree_def test_rel, expr_simp)

lemma wlp_test [wp]: "wlp (test S) P = (S \<longrightarrow> P)\<^sub>e"
  by (simp add: wlp_itree_def test_rel, expr_simp)

lemma wp_seq [wp]: "wp (S ;; R) P = wp S (wp R P)"
  by (auto simp add: wp_itree_def seq_rel)

lemma wp_seq': "wp (S ;; R) = wp S \<circ> wp R"
  by (auto simp add: wp_itree_def seq_rel fun_eq_iff)

lemma wp_foldr_seq: "wp (foldr (\<lambda> i D. C i ;; D) xs Skip) = foldr (\<lambda> i Q. wp (C i) \<circ> Q) xs id"
  by (induct xs, simp_all add: wp_Skip' wp_seq')

lemma wp_foldr_seq_term:
  assumes "\<And> x. pre (C x) = (True)\<^sub>e"
  shows "pre (foldr (\<lambda> i D. C i ;; D) xs Skip) = (True)\<^sub>e"
  using assms by (induct xs, simp_all add: wp_Skip' wp_seq')

lemma wlp_seq [wp]: "wlp (S ;; R) P = wlp S (wlp R P)"
  by (auto simp add: wlp_itree_def seq_rel)

lemma wp_cond [wp]: "wp (if B then C\<^sub>1 else C\<^sub>2 fi) P = ((B \<longrightarrow> wp C\<^sub>1 P) \<and> (\<not> B \<longrightarrow> wp C\<^sub>2 P))\<^sub>e"
  by (auto simp add: wp_itree_def cond_rel fun_eq_iff)

lemma wlp_cond [wp]: "wlp (if B then C\<^sub>1 else C\<^sub>2 fi) P = ((B \<longrightarrow> wlp C\<^sub>1 P) \<and> (\<not> B \<longrightarrow> wlp C\<^sub>2 P))\<^sub>e"
  by (auto simp add: wlp_itree_def cond_rel fun_eq_iff)

lemma wp_let [wp]: "wp (let x \<leftarrow> e in S x) b = (wp (S (e \<s>)) b)\<^sub>e"
  by (auto simp add: wp_itree_def let_itree_def itree_rel_defs retvals_def SEXP_def)

lemma wlp_let [wp]: "wlp (let x \<leftarrow> e in S x) b = (wlp (S (e \<s>)) b)\<^sub>e"
  by (auto simp add: wlp_itree_def let_itree_def itree_rel_defs retvals_def SEXP_def)

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

lemma wp_input_in_where [wp]: 
  "wb_prism c \<Longrightarrow> wp_itree (input_in_where c A S) P = [\<lambda> s. \<exists> v\<in>A s. fst (S v) s \<and> wp_itree (snd (S v)) P s]\<^sub>e"
  by (auto simp add: wp_itree_def itree_rel fun_eq_iff)

lemma wlp_input_in_where [wp]: 
  "wb_prism c \<Longrightarrow> wlp_itree (input_in_where c A S) P = [\<lambda> s. \<forall> v\<in>A s. fst (S v) s \<longrightarrow> wlp_itree (snd (S v)) P s]\<^sub>e"
  by (auto simp add: wlp_itree_def itree_rel fun_eq_iff)

lemma pre_itree_promote [wp, code_unfold]: 
  "mwb_lens a \<Longrightarrow> pre (C \<Up>\<Up> a) = ((pre C) \<up> a \<and> \<^bold>D(a))\<^sub>e"
  by (expr_auto add: wp_itree_def itree_rel_def itree_pred)
     (metis mwb_lens_weak weak_lens_def)

method wp uses add = (simp add: prog_defs wp usubst_eval add)

end