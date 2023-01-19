section \<open> Total Correctness Hoare Logic \<close>

theory ITree_THoare
  imports ITree_Hoare
begin

text \<open> Total correctness = partial correctness + termination. Termination is expressed using 
  the weakest precondition calculus, i.e. @{term "pre S"} is the weakest precondition under
  which @{term S} terminates. \<close>

definition thoare_triple :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"thoare_triple P S Q = (hoare_triple P S Q \<and> `P \<longrightarrow> pre S`)"

syntax
  "_thoare"          :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("H[_]/ _/ [_]")

translations
  "_thoare P S Q" == "CONST thoare_triple (P)\<^sub>e S (Q)\<^sub>e"

lemma thoare_then_hoare: "H[P] C [Q] \<Longrightarrow> H{P} C {Q}"
  by (simp add: thoare_triple_def)

lemma thoareI: "\<lbrakk> H{P} C {Q}; `P \<longrightarrow> pre C` \<rbrakk> \<Longrightarrow> H[P] C [Q]"
  by (simp add: thoare_triple_def)

lemma thl_conseq:
  assumes "H[P\<^sub>2] S [Q\<^sub>2]" "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`Q\<^sub>2 \<longrightarrow> Q\<^sub>1`"
  shows "H[P\<^sub>1] S [Q\<^sub>1]"
  using assms 
  by (simp add: thoare_triple_def hoare_alt_def)
     (expr_auto, blast)

lemma thl_skip: "H[P] Skip [P]"
  by (auto simp add: thoare_triple_def hoare_alt_def terminates_Ret Skip_def)
     (metis (no_types, lifting) SEXP_def Skip_def tautI wp_Skip)

lemma thl_skip': 
  assumes "`P \<longrightarrow> Q`"
  shows "H[P] Skip [Q]"
  by (meson assms hl_skip' thl_skip thoare_triple_def)

lemma thl_seq: "\<lbrakk> H[P] S\<^sub>1 [Q]; H[Q] S\<^sub>2 [R] \<rbrakk> \<Longrightarrow> H[P] S\<^sub>1 ;; S\<^sub>2 [R]"
  by (auto simp add: thoare_triple_def hl_seq wp)
     (simp add: hoare_alt_def wp_alt_def seq_itree_def kleisli_comp_def, expr_auto, meson)

lemma thl_seq_inv [hoare_safe]: "\<lbrakk> H[P] S\<^sub>1 [P]; H[P] S\<^sub>2 [P] \<rbrakk> \<Longrightarrow> H[P] S\<^sub>1 ;; S\<^sub>2 [P]"
  by (simp add: thl_seq)

lemma thl_assigns: "H[\<sigma> \<dagger> P] \<langle>\<sigma>\<rangle>\<^sub>a [P]"
  by (simp add: thoare_triple_def hoare_assigns wp, subst_eval)

lemma thl_assign: "H[P\<lbrakk>e/x\<rbrakk>] x := e [P]"
  by (rule thl_assigns)

lemma thl_assigns_impl [hoare_safe]:
  assumes "`P \<longrightarrow> \<sigma> \<dagger> Q`"
  shows "H[P] \<langle>\<sigma>\<rangle>\<^sub>a [Q]"
  using assms by (auto intro: thl_conseq thl_assigns)

lemma thl_assign':
  assumes "`P \<longrightarrow> Q\<lbrakk>e/x\<rbrakk>`"
  shows "H[P] x := e [Q]"
  using assms by (fact thl_assigns_impl)

lemma thl_fwd_assign [hoare_safe]:
  assumes "vwb_lens x" "\<And> x\<^sub>0. H[$x = e\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> P\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>] S [Q]"
  shows "H[P] x := e ;; S [Q]"
  using assms
  by (auto simp add: thoare_triple_def hl_fwd_assign wp)
     (simp add: hoare_alt_def wp_alt_def, expr_auto
     ,metis assms(1) vwb_lens.put_eq vwb_lens_wb wb_lens_weak weak_lens_def)

lemma thl_assigns_bwd [hoare_safe]:
  assumes "H[P] S [\<sigma> \<dagger> Q]"
  shows "H[P] S ;; \<langle>\<sigma>\<rangle>\<^sub>a [Q]"
  by (blast intro: thl_seq[OF assms(1)] thl_assigns)

lemma thl_cond [hoare_safe]:
  assumes "H[B \<and> P] S [Q]" "H[\<not>B \<and> P] T [Q]"
  shows "H[P] if B then S else T fi [Q]"
  using assms by (simp add: thoare_triple_def hl_cond wp taut_def)

text \<open> For loops do not require a variant, as termination is guaranteed by construction \<close>

lemma thl_for:
  assumes "\<And> i. i < length xs \<Longrightarrow> H[@(R i)] S (xs ! i) [@(R (i+1))]"
  shows "H[@(R 0)] for i in xs do S i od [@(R (length xs))]"
  using assms 
  by (simp add: thoare_triple_def hl_for pre_terminates)
     (auto simp add: hoare_alt_def taut_def
     , metis (no_types, lifting) Suc_eq_plus1 terminates_for_itree)

lemma thl_for_inv [hoare_safe]:
  assumes "\<And> i. i < length xs \<Longrightarrow> H[@(R i)] S (xs ! i) [@(R (i+1))]"
    "`P \<longrightarrow> @(R 0)`" "`@(R (length xs)) \<longrightarrow> Q`"
  shows "H[P] for x in xs inv i. @(R i) do S x od [Q]"
  unfolding for_inv_def
  by (rule thl_conseq[OF thl_for[of xs R S, OF assms(1)]], simp_all add: assms)

lemma thl_for_to_inv [hoare_safe]:
  assumes "\<And>i. \<lbrakk> m \<le> i; i \<le> n \<rbrakk> \<Longrightarrow> H[@(R i)] S i [@(R (i + 1))]"
   "`P \<longrightarrow> @(R m)`" "`@(R (n+1 - m+m)) \<longrightarrow> Q`"
  shows "H[P] for i := m to n inv @(R i) do S i od [Q]"
  unfolding for_to_inv_def fst_conv snd_conv
  using assms
  apply (rule_tac thl_for_inv, simp_all only: length_upt)
  apply (metis ab_semigroup_add_class.add_ac(1) add.commute assms(1) le_add2 less_Suc_eq_le less_diff_conv nth_upt plus_1_eq_Suc)
  apply (simp add: assms(2))
  done 

lemma thl_while [hoare_safe]:
  fixes V :: "'s \<Rightarrow> 'a::wellorder"
  assumes "\<And> z. H[P \<and> B \<and> V = \<guillemotleft>z\<guillemotright>] S [P \<and> V < \<guillemotleft>z\<guillemotright>]"
  shows "H[P] while B do S od [\<not> B \<and> P]"
proof -
  from assms have "\<^bold>{P \<and> B\<^bold>} S \<^bold>{P\<^bold>}"
    by (auto simp add: hoare_alt_def thoare_triple_def)
  hence partial: "\<^bold>{P\<^bold>} while B do S od \<^bold>{\<not> B \<and> P\<^bold>}"
    by (rule hoare_while_partial)
  from assms have S_term: "\<And> s. \<lbrakk> B s; P s \<rbrakk> \<Longrightarrow> terminates (S s)"
    by (simp add: thoare_triple_def pre_terminates, simp add: hoare_alt_def taut_def)  
  from assms have wS_term: "`P \<longrightarrow> pre (while B do S od)`"
    by (auto simp add: pre_terminates taut_def thoare_triple_def hoare_alt_def) 
       (auto intro!: terminates_iterate_wellorder_variant[of B P S V] simp add: SEXP_def)
  show ?thesis
    using partial thoareI wS_term by fastforce
qed

definition while_inv_var :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 'a::wellorder) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
[code_unfold]: "while_inv_var B I V P = iterate B P"

syntax 
  "_while_inv_var_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("while _ inv _ var _ do _ od")
  "_while_inv_var_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("while _ invariant _ variant _ do _ od")
translations "_while_inv_var_itree B I V P" == "CONST while_inv_var (B)\<^sub>e (I)\<^sub>e (V)\<^sub>e P"

lemma thl_while_inv_var [hoare_safe]:
  assumes "\<And> z. H[I \<and> B \<and> V = \<guillemotleft>z\<guillemotright>] S [I \<and> V < \<guillemotleft>z\<guillemotright>]" "`P \<longrightarrow> I`" "`(\<not> B \<and> I) \<longrightarrow> Q`"
  shows "H[P] while B inv I var V do S od [Q]"
  unfolding while_inv_var_def
  by (auto intro!: thl_conseq[OF _ assms(2) assms(3)] thl_while assms(1))

text \<open> The next law is a degenerate partial correctness law, which ignores the variant. \<close>

lemma hl_while_inv_var [hoare_safe]:
  assumes "\<^bold>{I \<and> B\<^bold>} S \<^bold>{I\<^bold>}" "`P \<longrightarrow> I`" "`(\<not> B \<and> I) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>}while B inv I var V do S od\<^bold>{Q\<^bold>}"
proof -
  have "while B inv I var V do S od = while B inv I do S od"
    by (simp add: while_inv_var_def while_inv_def)
  with assms show ?thesis
    by (simp add: hl_while_inv)
qed

lemma thl_via_wlp_wp: "H[P] S [Q] = `P \<longrightarrow> (wlp S Q \<and> pre S)`"
  by (simp add: thoare_triple_def hl_via_wlp, expr_auto)

end