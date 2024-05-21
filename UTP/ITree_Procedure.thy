section \<open> Procedures \<close>

theory ITree_Procedure
  imports ITree_Circus ITree_Hoare ITree_THoare
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

abbreviation proc_ret_empty :: "'s \<Rightarrow> ('e, unit \<times> 's) itree" where
"proc_ret_empty \<equiv> proc_ret (())\<^sub>e"

lemma ret_rbind [simp]: "proc_ret e ;; rbind x = x := e"
  by (simp add: proc_ret_def rbind_def seq_itree_def kleisli_comp_def assigns_def expr_defs)

lemma ret_rbind' [simp]: "(P ;; proc_ret e) ;; rbind x = P ;; x := e"
  by (simp add: kcomp_assoc)

lemma ret_drop [simp]: "proc_ret e ;; rdrop = Skip"
  by (simp add: proc_ret_def rdrop_def Skip_def seq_itree_def kleisli_comp_def)

lemma ret_drop' [simp]: "(P ;; proc_ret e) ;; rdrop = P"
  by (simp add: kcomp_assoc)

syntax 
  "_call"      :: "svid \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("_ := <_ _>" [61, 0, 61] 61)
  "_call_nret" :: "id \<Rightarrow> logic \<Rightarrow> logic" ("call _ _" [0, 61] 61) 
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

lemma thl_proc_call [hoare_safe]: 
  assumes "\<And> v. H[P \<and> \<guillemotleft>v\<guillemotright> = e] C(v) ;; rbind x [Q]"
  shows "H[P] x := <C(e)> [Q]"
  using assms
  apply (auto simp add: thoare_triple_def hl_proc_call wp)
  apply (auto simp add: proc_call_def taut_def seq_itree_def kleisli_comp_def)
  apply (metis (mono_tags, lifting) SEXP_def kleisli_comp_def pre_terminates seq_itree_def wp_seq)
  done

lemma hl_proc_call_nret [hoare_safe]: 
  assumes "\<And> v. H{P \<and> \<guillemotleft>v\<guillemotright> = e} C(v) ;; rdrop {Q}"
  shows "H{P} call C(e) {Q}"
  using assms
  by (auto simp add: hoare_alt_def proc_call_nret_def seq_itree_def kleisli_comp_def)

lemma thl_proc_call_nret [hoare_safe]: 
  assumes "\<And> v. H[P \<and> \<guillemotleft>v\<guillemotright> = e] C(v) ;; rdrop [Q]"
  shows "H[P] call C(e) [Q]"
  using assms
  apply (auto simp add: thoare_triple_def hl_proc_call_nret wp)
  apply (auto simp add: proc_call_nret_def taut_def seq_itree_def kleisli_comp_def)
  apply (metis (mono_tags, lifting) SEXP_def kleisli_comp_def pre_terminates seq_itree_def wp_seq)
  done

ML_file \<open>ITree_Procedure.ML\<close>

end