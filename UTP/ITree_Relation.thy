subsection \<open> Relational Abstraction \<close>

theory ITree_Relation
  imports ITree_Circus
begin

text \<open> The relational abstraction captures the possible return values associated with particular
  inputs to a Kleisli tree. It ignores any visible events and treats them as nondeterminism,
  if present. \<close>

definition itree_rel :: "('e, 'a, 'b) ktree \<Rightarrow> ('a \<times> 'b) set" where
"itree_rel P = {(s, s'). s' \<in> \<^bold>R (P s)}"

named_theorems rel

definition spec :: "'s scene \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 's rel" where
"spec a pre post = {(s, s'). s \<approx>\<^sub>S s' on (- a) \<and> pre s \<longrightarrow> post s'}"

lemma assume_rel [rel]: "itree_rel (assume P) = {(s, s'). s' = s \<and> P s}"
  apply (auto simp add: itree_rel_def retvals_def assume_def)
  apply (metis (full_types) Ret_trns diverge_no_Ret_trans itree.inject(1))
  using diverge_no_Ret_trans apply fastforce
  done

lemma test_rel [rel]: "itree_rel (test P) = {(s, s'). s' = s \<and> P s}"
  apply (auto simp add: itree_rel_def retvals_def test_def)
  apply (metis (full_types) empty_iff insert_iff retvals_Ret retvals_deadlock retvals_traceI)
  using nonterminates_iff apply force
  done

lemma Skip_rel [rel]: "itree_rel Skip = Id"
  by (auto simp add: itree_rel_def retvals_def Skip_def)

lemma assigns_rel [rel]: "itree_rel \<langle>\<sigma>\<rangle>\<^sub>a = {(s, s'). s' = \<sigma> s}"
  by (auto simp add: itree_rel_def retvals_def assigns_def)

lemma Div_rel [rel]: "itree_rel Div = {}"
  by (simp add: itree_rel_def)

lemma Stop_rel [rel]: "itree_rel Stop = {}"
  by (simp add: itree_rel_def)

lemma seq_rel [rel]: "itree_rel (P \<Zcomp> Q) = itree_rel P O itree_rel Q"
  by (auto simp add: kleisli_comp_def itree_rel_def relcomp_unfold)

lemma cond_rel [rel]: 
  "itree_rel (if B then C\<^sub>1 else C\<^sub>2 fi) 
    = {(s\<^sub>1, s\<^sub>2). if (B s\<^sub>1) then (s\<^sub>1, s\<^sub>2) \<in> itree_rel C\<^sub>1 else (s\<^sub>1, s\<^sub>2) \<in> itree_rel C\<^sub>2}"
  by (auto simp add: cond_itree_def itree_rel_def)

lemma input_in_rel [rel]: 
  "wb_prism c \<Longrightarrow> itree_rel (input_in c A P) = {(s, s'). \<exists> v \<in> A s. (s, s') \<in> itree_rel (P v)}" 
  by (auto simp add: input_in_where_def itree_rel_def retvals_inp_in)

lemma input_rel [rel]: "wb_prism c \<Longrightarrow> itree_rel (input c P) = (\<Union> v. itree_rel (P v))"
  by (auto simp add: input_in_rel)

lemma input_in_lit_rel [rel]: "wb_prism c \<Longrightarrow> itree_rel (input_in c (\<guillemotleft>A\<guillemotright>)\<^sub>e P) = (\<Union> v \<in> A. itree_rel (P v))"
  by (auto simp add: input_in_rel)

end