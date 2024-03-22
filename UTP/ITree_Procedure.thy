section \<open> Procedures \<close>

theory ITree_Procedure
  imports ITree_Circus ITree_Hoare
  keywords "over"
begin

definition proc_call :: 
  "('r \<Longrightarrow> 's) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> ('e, 'r \<times> 's) itree) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) htree" where
[code_unfold]: 
  "proc_call x pr prm = (\<lambda> s. pr (prm s) s \<bind> (\<lambda> (r, s\<^sub>0). Ret (put\<^bsub>x\<^esub> s\<^sub>0 r)))"

definition proc_call_nret :: 
  "('a \<Rightarrow> 's \<Rightarrow> ('e, 'r \<times> 's) itree) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) htree" where
  [code_unfold]: 
  "proc_call_nret pr prm = (\<lambda> s. pr (prm s) s \<bind> (\<lambda> (r, s\<^sub>0). Ret s\<^sub>0))"

definition proc_ret :: "('s \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> ('e, 'a \<times> 's) itree" where 
  "proc_ret e = (\<lambda> s. Ret (e s, s))"

syntax 
  "_call"      :: "svid \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("_ := call _ _" [61, 0, 61] 61)
  "_call_nret" :: "id \<Rightarrow> logic \<Rightarrow> logic" ("call _ _") 
  "_return"    :: "logic \<Rightarrow> logic" ("return")

translations 
  "_return e" == "CONST proc_ret (e)\<^sub>e"
  "_call x P e" == "CONST proc_call x P (e)\<^sub>e"
  "_call_nret P e" == "CONST proc_call_nret P (e)\<^sub>e"

lemma hl_procedure_call [hoare_safe]: 
  assumes "\<And> v. H{P \<and> \<guillemotleft>v\<guillemotright> = e} C(v) {Q}"
  shows "H{P} call C(e) {Q}"
  using assms
  by (auto simp add: hoare_alt_def procedure_call_def)

ML_file \<open>ITree_Procedure.ML\<close>

end