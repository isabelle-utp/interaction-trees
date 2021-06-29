subsection \<open> Relational Abstraction \<close>

theory ITree_Relation
  imports ITree_Circus "Shallow-Expressions.Shallow_Expressions"
begin

text \<open> The relational abstraction captures the possible return values associated with particular
  inputs to a Kleisli tree. It ignores any visible events and treats them as nondeterminism,
  if present. \<close>

definition itree_rel :: "('e, 's) htree \<Rightarrow> 's rel" where
"itree_rel P = {(s, s'). s' \<in> \<^bold>R (P s)}"

text \<open> The precondition captures the initial states that give the possibility of divergence. \<close>

definition itree_pre :: "('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool)" where
"itree_pre P = (\<lambda> s. \<not> (\<exists> es. P s \<midarrow>es\<leadsto> diverge))"

lemma assigns_rel: "itree_rel \<langle>\<sigma>\<rangle>\<^sub>a = {(s, s'). s' = \<sigma> s}"
  by (auto simp add: itree_rel_def retvals_def assigns_def)

lemma assigns_pre: "itree_pre \<langle>\<sigma>\<rangle>\<^sub>a = (True)\<^sub>e"
  by (auto simp add: itree_pre_def assigns_def)

lemma Div_rel: "itree_rel Div = {}"
  by (simp add: itree_rel_def)

lemma Div_pre: "itree_pre Div = (False)\<^sub>e"
  by (auto simp add: itree_pre_def fun_eq_iff)

lemma Stop_rel: "itree_rel Stop = {}"
  by (simp add: itree_rel_def)

lemma Stop_pre: "itree_pre Stop = (True)\<^sub>e"
  by (auto simp add: itree_pre_def fun_eq_iff deadlock_def)

lemma seq_rel: "itree_rel (P \<Zcomp> Q) = itree_rel P O itree_rel Q"
  by (auto simp add: itree_rel_def relcomp_unfold)

lemma inp_in_rel: "wb_prism c \<Longrightarrow> itree_rel (input_in c A P) = {(s, s'). \<exists> v. v \<in> A s \<and> (s, s') \<in> itree_rel (P v)}" 
  by (auto simp add: input_in_def itree_rel_def retvals_inp_in)

definition spec :: "'s scene \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 's rel" where
"spec a pre post = {(s, s'). s \<approx>\<^sub>S s' on (- a) \<and> pre s \<longrightarrow> post s'}"

definition hoare_triple :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"hoare_triple P S Q = (spec \<top>\<^sub>S P Q \<subseteq> itree_rel S)"

end