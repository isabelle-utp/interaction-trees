section \<open> Procedures \<close>

theory ITree_Procedure
  imports ITree_Circus ITree_Hoare
  keywords "over"
begin

definition "rbind x = (\<lambda> (r, s). Ret (put\<^bsub>x\<^esub> s r))"

definition "rdrop = (\<lambda> (r, s). Ret s)"

definition proc_call :: 
  "('r \<Longrightarrow> 's) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> ('e, 'r \<times> 's) itree) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) htree" where
[code_unfold]: 
  "proc_call x pr prm = (\<lambda> s. pr (prm s) s \<bind> rbind x)"

definition proc_call_nret :: 
  "('a \<Rightarrow> 's \<Rightarrow> ('e, 'r \<times> 's) itree) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) htree" where
  [code_unfold]: 
  "proc_call_nret pr prm = (\<lambda> s. pr (prm s) s \<bind> rdrop)"

definition proc_ret :: "('s \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> ('e, 'a \<times> 's) itree" where 
  "proc_ret e = (\<lambda> s. Ret (e s, s))"

lemma ret_rbind: "proc_ret e ;; rbind x = x := e"
  by (simp add: proc_ret_def rbind_def seq_itree_def kleisli_comp_def assigns_def expr_defs)

lemma ret_drop: "proc_ret e ;; rdrop = Skip"
  by (simp add: proc_ret_def rdrop_def Skip_def seq_itree_def kleisli_comp_def)

syntax 
  "_call"      :: "svid \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("_ := <_ _>" [61, 0, 61] 61)
  "_call_nret" :: "id \<Rightarrow> logic \<Rightarrow> logic" ("call _ _") 
  "_return"    :: "logic \<Rightarrow> logic" ("return")

translations 
  "_return e" == "CONST proc_ret (e)\<^sub>e"
  "_call x P e" == "CONST proc_call x P (e)\<^sub>e"
  "_call_nret P e" == "CONST proc_call_nret P (e)\<^sub>e"

lemma hl_proc_call [hoare_safe]: 
  assumes "\<And> v. H{P \<and> \<guillemotleft>v\<guillemotright> = e} C(v) ;; rbind x {Q}"
  shows "H{P} x := <C(e)> {Q}"
  using assms
  by (auto simp add: hoare_alt_def proc_call_def seq_itree_def kleisli_comp_def)

lemma hl_proc_call_nret [hoare_safe]: 
  assumes "\<And> v. H{P \<and> \<guillemotleft>v\<guillemotright> = e} C(v) ;; rdrop {Q}"
  shows "H{P} call C(e) {Q}"
  using assms
  by (auto simp add: hoare_alt_def proc_call_nret_def seq_itree_def kleisli_comp_def)

ML_file \<open>ITree_Procedure.ML\<close>

end