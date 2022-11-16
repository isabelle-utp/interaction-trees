section \<open> Total Correctness Hoare Logic \<close>

theory ITree_THoare
  imports ITree_Hoare
begin

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

lemma thl_assigns: "H[\<sigma> \<dagger> P] \<langle>\<sigma>\<rangle>\<^sub>a [P]"
  by (simp add: thoare_triple_def hoare_assigns wp, subst_eval)

lemma thl_assign: "H[P\<lbrakk>e/x\<rbrakk>] x := e [P]"
  by (rule thl_assigns)

lemma thl_cond [hoare_safe]:
  assumes "H[B \<and> P] S [Q]" "H[\<not>B \<and> P] T [Q]"
  shows "H[P] if B then S else T fi [Q]"
  using assms by (simp add: thoare_triple_def hl_cond wp taut_def)

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

lemma thl_via_wlp_wp: "H[P] S [Q] = `P \<longrightarrow> (wlp S Q \<and> pre S)`"
  by (simp add: thoare_triple_def hl_via_wlp, expr_auto)

end