subsection \<open> Relational Abstraction \<close>

theory ITree_Relation
  imports ITree_Circus
begin

text \<open> The relational abstraction captures the possible return values associated with particular
  inputs to a Kleisli tree. It ignores any visible events and treats them as nondeterminism,
  if present. \<close>

definition itree_rel :: "('e, 's) htree \<Rightarrow> 's rel" where
"itree_rel P = {(s, s'). s' \<in> \<^bold>R (P s)}"

text \<open> The precondition captures the initial states that give the possibility of divergence. \<close>

definition itree_pre :: "('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool)" where
"itree_pre P = (\<lambda> s. \<not> (\<exists> es. P s \<midarrow>es\<leadsto> diverge))"

expr_ctr itree_pre

definition refined_by :: "('e, 's) htree \<Rightarrow> ('e, 's) htree \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
"refined_by P Q = (`itree_pre P \<longrightarrow> itree_pre Q` \<and> {(s, s') \<in> itree_rel Q. itree_pre P s} \<subseteq> itree_rel P)"

definition spec :: "'s scene \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 's rel" where
"spec a pre post = {(s, s'). s \<approx>\<^sub>S s' on (- a) \<and> pre s \<longrightarrow> post s'}"

definition hoare_triple :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"hoare_triple P S Q = (itree_rel S \<subseteq> spec \<top>\<^sub>S P Q)"

syntax "_hoare" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>{_\<^bold>} _ \<^bold>{_\<^bold>}")
translations "_hoare P S Q" == "CONST hoare_triple (P)\<^sub>e S (Q)\<^sub>e"

lemma hoare_alt_def: "\<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>} \<longleftrightarrow> (\<forall> s s' es. P s \<and> S s \<midarrow>es\<leadsto> Ret s' \<longrightarrow> Q s')"
  by (auto simp add: hoare_triple_def spec_def itree_rel_def retvals_def subset_iff)

named_theorems wp

definition wlp_itree :: "('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool)" where
"wlp_itree S P = (\<lambda>s. \<forall>s'. (s, s') \<in> itree_rel S \<longrightarrow> P s')"

expr_ctr wlp_itree

syntax "_wlp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("wlp")
translations "_wlp S P" == "CONST wlp_itree S (P)\<^sub>e"

lemma wlp_true [wp]: "wlp P True = (True)\<^sub>e"
  by (expr_simp add: wlp_itree_def)
  
lemma assigns_rel: "itree_rel \<langle>\<sigma>\<rangle>\<^sub>a = {(s, s'). s' = \<sigma> s}"
  by (auto simp add: itree_rel_def retvals_def assigns_def)

lemma assigns_pre: "itree_pre \<langle>\<sigma>\<rangle>\<^sub>a = (True)\<^sub>e"
  by (auto simp add: itree_pre_def assigns_def)

lemma Div_rel: "itree_rel Div = {}"
  by (simp add: itree_rel_def)

lemma Div_pre: "itree_pre Div = (False)\<^sub>e"
  by (auto simp add: itree_pre_def fun_eq_iff)

lemma Div_wlp: "wlp Div P = (True)\<^sub>e"
  by (simp add: wlp_itree_def Div_rel, expr_simp)


lemma Div_bottom: "Div \<sqsubseteq> P"
  by (simp add: refined_by_def Div_rel Div_pre)

lemma Stop_rel: "itree_rel Stop = {}"
  by (simp add: itree_rel_def)

lemma Stop_pre: "itree_pre Stop = (True)\<^sub>e"
  by (auto simp add: itree_pre_def fun_eq_iff deadlock_def)

lemma seq_pre: "itree_pre (P \<Zcomp> Q) = (itree_pre P \<and> wlp P (itree_pre Q))\<^sub>e"
  apply (expr_simp, auto elim!: trace_to_bindE simp add: itree_pre_def wlp_itree_def itree_rel_def retvals_def)
  apply (metis bind_diverge trace_to_bind_left)
  apply (meson trace_to_bind)
  apply (metis trace_of_Sils trace_to_Nil trace_to_trans)
  done

lemma seq_rel: "itree_rel (P \<Zcomp> Q) = itree_rel P O itree_rel Q"
  by (auto simp add: itree_rel_def relcomp_unfold)

lemma input_in_rel: "wb_prism c \<Longrightarrow> itree_rel (input_in c A P) = {(s, s'). \<exists> v \<in> A s. (s, s') \<in> itree_rel (P v)}" 
  by (auto simp add: input_in_def itree_rel_def retvals_inp_in)

lemma input_rel: "wb_prism c \<Longrightarrow> itree_rel (input c P) = (\<Union> v. itree_rel (P v))"
  by (auto simp add: input_in_rel input_alt_def)

lemma input_in_lit_rel: "wb_prism c \<Longrightarrow> itree_rel (input_in c (\<guillemotleft>A\<guillemotright>)\<^sub>e P) = (\<Union> v \<in> A. itree_rel (P v))"
  by (auto simp add: input_in_rel input_alt_def)

end