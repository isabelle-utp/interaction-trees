subsection \<open> Relational Abstraction \<close>

theory ITree_Relation
  imports ITree_Circus UTP2.utp
begin

unbundle UTP_Logic_Syntax

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
"spec a P Q = {(s, s'). s \<approx>\<^sub>S s' on (- a) \<and> P s \<longrightarrow> Q s'}"

lemma assume_rel [itree_rel]: "itree_rel (assume P) = {(s, s'). s' = s \<and> P s}"
  apply (auto simp add: itree_rel_defs retvals_def assume_def)
  apply (metis (full_types) Ret_trns diverge_no_Ret_trans itree.inject(1))
  using diverge_no_Ret_trans apply fastforce
  done

term ITree_Circus.test 
term test


no_syntax "_assume" :: "logic \<Rightarrow> logic" ("\<questiondown>_?")

no_translations "\<questiondown>P?" == "CONST test (P)\<^sub>e"

consts utest :: "('s \<Rightarrow> bool) \<Rightarrow> 'p"

translations "\<questiondown>P?" == "CONST utest (P)\<^sub>e"

adhoc_overloading utest ITree_Circus.test and utest test


lemma test_pred [itree_pred]: "\<lbrakk>\<questiondown>P?\<rbrakk>\<^sub>p = \<questiondown>P?"
  apply (simp add: itree_pred_def)
  apply (simp add: ITree_Circus.test_def)
  apply (simp add: test_def fun_eq_iff)
  done

lemma assume_pred [itree_pred]: "\<lbrakk>(ITree_Circus.assume P)\<rbrakk>\<^sub>p = test P"
  apply (simp add: itree_pred_def)
  apply (simp add: ITree_Circus.assume_def)
  apply (simp add: test_def fun_eq_iff)
  done


 lemma test_rel [itree_rel]: "itree_rel (ITree_Circus.test P) = {(s, s'). s' = s \<and> P s}"
  apply (auto simp add: itree_rel_defs retvals_def ITree_Circus.test_def)

  apply (metis (full_types) empty_iff insert_iff retvals_Ret retvals_deadlock retvals_traceI)
  using nonterminates_iff apply force
  done
 
lemma Skip_rel [itree_rel]: "itree_rel Skip = Id"
  by (auto simp add: itree_rel_defs retvals_def Skip_def)

no_notation assigns ("\<langle>_\<rangle>\<^sub>a")

adhoc_overloading uassigns assigns

lemma assigns_pred [itree_pred]: "\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>p (s, s') = (s' = \<sigma> s)"
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

lemma cond_pred [itree_pred]: 
  "\<lbrakk>cond_itree C\<^sub>1 B C\<^sub>2\<rbrakk>\<^sub>p (s, s') = (if B s then \<lbrakk>C\<^sub>1\<rbrakk>\<^sub>p (s, s') else \<lbrakk>C\<^sub>2\<rbrakk>\<^sub>p (s, s'))"
  by (auto simp add: cond_itree_def itree_rel_defs)

lemma cond_rel [itree_rel]: 
  "itree_rel (if B then C\<^sub>1 else C\<^sub>2 fi) 
    = {(s\<^sub>1, s\<^sub>2). if (B s\<^sub>1) then (s\<^sub>1, s\<^sub>2) \<in> itree_rel C\<^sub>1 else (s\<^sub>1, s\<^sub>2) \<in> itree_rel C\<^sub>2}"
  by (auto simp add: cond_itree_def itree_rel_defs)

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

ML_file \<open>Lens_Rel_Utils.ML\<close>

method rename_rel_alpha_vars = tactic \<open> Lens_Rel_Utils.rename_rel_alpha_vars \<close>

method itree_pred uses add = (expr_simp add: prog_defs itree_pred add; ((rule allI)+)?; rename_rel_alpha_vars)
                
end