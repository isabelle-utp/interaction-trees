subsection \<open> Relational Abstraction \<close>

theory ITree_Relation
  imports ITree_Circus
begin

text \<open> The relational abstraction captures the possible return values associated with particular
  inputs to a Kleisli tree. It ignores any visible events and treats them as nondeterminism,
  if present. \<close>

definition itree_pred :: "('e, 'a, 'b) ktree \<Rightarrow> (bool, 'a \<times> 'b) expr" ("\<lbrakk>_\<rbrakk>\<^sub>p") where
"itree_pred P = (\<lambda> (s, s'). s' \<in> \<^bold>R (P s))"

definition itree_rel :: "('e, 'a, 'b) ktree \<Rightarrow> ('a \<times> 'b) set" where
"itree_rel P = Collect (itree_pred P)"

lemmas itree_rel_defs = itree_pred_def itree_rel_def

named_theorems itree_pred and itree_rel

definition spec :: "'s scene \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 's rel" where
"spec a pre post = {(s, s'). s \<approx>\<^sub>S s' on (- a) \<and> pre s \<longrightarrow> post s'}"

lemma assume_rel [itree_rel]: "itree_rel (assume P) = {(s, s'). s' = s \<and> P s}"
  apply (auto simp add: itree_rel_defs retvals_def assume_def)
  apply (metis (full_types) Ret_trns diverge_no_Ret_trans itree.inject(1))
  using diverge_no_Ret_trans apply fastforce
  done

lemma test_rel [itree_rel]: "itree_rel (test P) = {(s, s'). s' = s \<and> P s}"
  apply (auto simp add: itree_rel_defs retvals_def test_def)
  apply (metis (full_types) empty_iff insert_iff retvals_Ret retvals_deadlock retvals_traceI)
  using nonterminates_iff apply force
  done

lemma Skip_pred [itree_rel]: "itree_pred Skip = (\<lambda> (s, s'). s = s')"
  by (auto simp add: itree_rel_defs retvals_def Skip_def)

lemma Skip_rel [itree_rel]: "itree_rel Skip = Id"
  by (auto simp add: itree_rel_defs retvals_def Skip_def)

lemma assigns_pred [itree_pred]: "\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>p = (\<lambda> (s, s'). s' = \<sigma> s)"
  by (auto simp add: itree_rel_defs retvals_def assigns_def)

lemma assigns_rel [itree_rel]: "itree_rel \<langle>\<sigma>\<rangle>\<^sub>a = {(s, s'). s' = \<sigma> s}"
  by (simp add: itree_rel_def set_eq_iff assigns_pred)

lemma Div_rel [itree_rel]: "itree_rel Div = {}"
  by (simp add: itree_rel_defs)

lemma Stop_pred [itree_pred]: "\<lbrakk>Stop\<rbrakk>\<^sub>p (s, s') = False"
  by (auto simp add: itree_rel_defs)

lemma Stop_rel [itree_rel]: "itree_rel Stop = {}"
  by (simp add: itree_rel_def set_eq_iff Stop_pred)

lemma seq_pred [itree_pred]: "\<lbrakk>P ;; Q\<rbrakk>\<^sub>p (s, s') = (\<exists> s\<^sub>0.  \<lbrakk>P\<rbrakk>\<^sub>p (s, s\<^sub>0) \<and> \<lbrakk>Q\<rbrakk>\<^sub>p (s\<^sub>0, s'))"
  by (auto simp add: itree_rel_defs seq_itree_def kleisli_comp_def)

lemma seq_rel [itree_rel]: "itree_rel (P ;; Q) = itree_rel P O itree_rel Q"
  by (auto simp add: seq_itree_def kleisli_comp_def itree_rel_defs relcomp_unfold)

lemma cond_itree_pred [itree_pred]: 
  "\<lbrakk>P \<lhd> b \<rhd> Q\<rbrakk>\<^sub>p = (\<lambda> (s, s'). if b s then \<lbrakk>P\<rbrakk>\<^sub>p (s, s') else \<lbrakk>Q\<rbrakk>\<^sub>p (s, s'))"
  by (auto simp add: cond_itree_def itree_rel_defs)

lemma cond_rel [itree_rel]: 
  "itree_rel (if B then C\<^sub>1 else C\<^sub>2 fi) 
    = {(s\<^sub>1, s\<^sub>2). if (B s\<^sub>1) then (s\<^sub>1, s\<^sub>2) \<in> itree_rel C\<^sub>1 else (s\<^sub>1, s\<^sub>2) \<in> itree_rel C\<^sub>2}"
  by (auto simp add: cond_itree_def itree_rel_defs)

lemma iterate_pred [itree_pred]: 
  "\<lbrakk>iterate P C\<rbrakk>\<^sub>p = (\<lambda> (s, s'). (\<not> P s \<and> s = s') \<or> (\<exists> es. P s \<and> (P, s) \<turnstile> C \<midarrow>es\<leadsto>\<^sub>\<checkmark> s' \<and> \<not> P s'))"
  by (simp add: itree_pred_def retvals_iterate)

lemma itree_while_pred: 
  "\<lbrakk>while P do C od\<rbrakk>\<^sub>p (s, s') = 
   ((s = s' \<or> (\<exists>xs. xs \<noteq> [] \<and> (\<forall>i<length xs. P ((s # xs) ! i) \<and> \<lbrakk>C\<rbrakk>\<^sub>p ((s # xs) ! i, xs ! i)) \<and> s' = last xs)) \<and> \<not> P s')"
  by (simp add: iterate_pred itree_chain_iff_rtc_chain, simp add: itree_pred_def)

lemma input_in_where_rel [itree_rel]: 
  "wb_prism c \<Longrightarrow> itree_rel (input_in_where c A P) = {(s, s'). \<exists> v \<in> A s. fst (P v) s \<and> (s, s') \<in> itree_rel (snd (P v))}" 
  by (auto simp add: input_in_where_def itree_rel_defs retvals_inp_in_where)

lemma input_in_pred [itree_pred]: 
  "wb_prism c \<Longrightarrow> \<lbrakk>input_in c A P\<rbrakk>\<^sub>p (s, s') = (\<exists> v \<in> A s. \<lbrakk>P v\<rbrakk>\<^sub>p (s, s'))" 
  by (auto simp add: input_in_where_def itree_rel_defs retvals_inp_in)

lemma input_in_rel [itree_rel]: 
  "wb_prism c \<Longrightarrow> itree_rel (input_in c A P) = {(s, s'). \<exists> v \<in> A s. (s, s') \<in> itree_rel (P v)}" 
  by (auto simp add: input_in_where_def itree_rel_defs retvals_inp_in)

lemma input_rel [itree_rel]: "wb_prism c \<Longrightarrow> itree_rel (input c P) = (\<Union> v. itree_rel (P v))"
  by (auto simp add: input_in_rel)

lemma input_in_lit_rel [itree_rel]: "wb_prism c \<Longrightarrow> itree_rel (input_in c (\<guillemotleft>A\<guillemotright>)\<^sub>e P) = (\<Union> v \<in> A. itree_rel (P v))"
  by (auto simp add: input_in_rel)

lemma promote_rel [itree_pred]: 
  "mwb_lens a \<Longrightarrow> \<lbrakk>P \<Up>\<Up> a\<rbrakk>\<^sub>p (s, s') = (s \<in> \<S>\<^bsub>a\<^esub> \<and> \<lbrakk>P\<rbrakk>\<^sub>p (get\<^bsub>a\<^esub> s, get\<^bsub>a\<^esub> s') \<and> s \<oplus>\<^sub>L s' on a = s')"
  by (auto elim!: trace_to_bindE bind_RetE' simp add: itree_pred_def retvals_def promote_itree_def lens_override_def)
     (metis bind_Ret trace_to_bind_left)

ML_file \<open>Lens_Rel_Utils.ML\<close>

method rename_rel_alpha_vars = tactic \<open> Lens_Rel_Utils.rename_rel_alpha_vars \<close>

method itree_pred uses add = (simp add: prog_defs itree_pred add; expr_simp add: prog_defs itree_pred add; ((rule allI)+)?; rename_rel_alpha_vars)

end