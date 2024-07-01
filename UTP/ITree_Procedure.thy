section \<open> Procedures \<close>

theory ITree_Procedure
  imports ITree_Circus ITree_Hoare ITree_THoare ITree_DFP
  keywords "over"
begin

subsection \<open> Modelling Procedures \<close>

text \<open> Procedures are implemented by having heterogeneous ITrees with a pair return type 
  @{typ "'a \<times> 's"}, where @{typ "'s"} is the state and @{typ "'a"} is the return type. The
  following type models a procedure with input @{typ "'a"}, return type @{typ "'r"}, 
  and state type @{typ "'s"}. \<close>

type_synonym ('a, 'r, 's, 'e) iproc = "'a \<Rightarrow> 's \<Rightarrow> ('e, 'r \<times> 's) itree"

subsection \<open> Constructors \<close>

text \<open> Bind a return value to a lens \<close>

definition rbind :: "('a \<Longrightarrow> 's) \<Rightarrow> 'a \<times> 's \<Rightarrow> ('e, 's) itree" where 
"rbind x = (\<lambda> (r, s). Ret (put\<^bsub>x\<^esub> s r))"

text \<open> Drop a return value \<close>

definition rdrop :: "'a \<times> 's \<Rightarrow> ('e, 's) itree" where
"rdrop = (\<lambda> (r, s). Ret s)"

text \<open> Call a procedure with a variable to store the return value, and expression to provide
  the inputs. \<close>

definition proc_call :: 
  "('r \<Longrightarrow> 's) \<Rightarrow> ('a, 'r, 's, 'e) iproc \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) htree" where
[code_unfold]: 
  "proc_call x pr prm = (\<lambda> s. pr (prm s) s \<bind> rbind x)"

text \<open> Call a procedure without binding the return value. \<close>

definition proc_call_nret :: 
  "('a \<Rightarrow> 's \<Rightarrow> ('e, 'r \<times> 's) itree) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) htree" where
  [code_unfold]: 
  "proc_call_nret pr prm = (\<lambda> s. pr (prm s) s \<bind> rdrop)"

text \<open> Return statements in an ITree procedure \<close>

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

text \<open> Output the return value of a procedure as an event \<close>

definition output_return :: "('s \<Rightarrow> ('e, 'a \<times> 's) itree) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 's) htree" where
"output_return P c = (\<lambda> s. P(s) \<bind> (\<lambda> (v, s'). outp c v \<then> Ret s'))" 

subsection \<open> Syntax \<close>

syntax 
  "_call"      :: "svid \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("_ := <_ _>" [61, 0, 61] 61)
  "_call_nret" :: "id \<Rightarrow> logic \<Rightarrow> logic" ("call _ _" [0, 61] 61) 
  "_return"    :: "logic \<Rightarrow> logic" ("return")

translations 
  "_return e" == "CONST proc_ret (e)\<^sub>e"
  "_call x P e" == "CONST proc_call x P (e)\<^sub>e"
  "_call_nret P e" == "CONST proc_call_nret P (e)\<^sub>e"

ML_file \<open>ITree_Procedure.ML\<close>

subsection \<open> Hoare logic \<close>

text \<open> We implement a specialised form of Hoare triple, which accepts a procedure as the program.
  The postcondition introduces a variable, to which the return value of the procedure is bound.
  Otherwise, the postcondition is the same as a normal Hoare triple. \<close>

definition hoare_rel_proc_triple :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> ('e, 'a \<times> 's) itree) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" where
"hoare_rel_proc_triple P C Q = (\<forall> s s' r es. P s \<and> C s \<midarrow>es\<leadsto> \<checkmark> (r, s') \<longrightarrow> Q r s s')"

syntax   
  "_hoare_proc" :: "logic \<Rightarrow> logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("(2H{_} /_) /{_./ _}")

translations
  "H{P} C {x. Q}" => "CONST hoare_rel_proc_triple (P)\<^sub>e C (\<lambda> x _ghost_old. (Q)\<^sub>e)"
  "H{P} C {x. Q}" <= "CONST hoare_rel_proc_triple (P)\<^sub>e C (\<lambda> x g. (Q)\<^sub>e)"

lemma hl_proc_conseq:
  assumes "H{P\<^sub>2} S {ret. @(Q\<^sub>2 ret)}" "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "\<And> ret. `@(Q\<^sub>2 ret) \<longrightarrow> @(Q\<^sub>1 ret)`"
  shows "H{P\<^sub>1} S {ret. @(Q\<^sub>1 ret)}"
  using assms by (auto simp add: hoare_rel_proc_triple_def, expr_simp, force)

lemma hl_return: 
  "H{P} return e {ret. \<guillemotleft>ret\<guillemotright> = e \<and> P}"
  by (simp add: hoare_rel_proc_triple_def proc_ret_def)

lemma hl_return' [hoare_safe]:
  assumes "\<And> ret. `\<guillemotleft>ret\<guillemotright> = e \<and> P \<longrightarrow> @(Q ret)`"
  shows "H{P} return e {ret. @(Q ret)}"
  by (force intro: hl_proc_conseq[where P\<^sub>2="P"] hl_return assms)

lemma hl_proc_seq:
  assumes "H{P} C\<^sub>1 {Q}" "H{Q} C\<^sub>2 {ret. @(R ret)}"
  shows "H{P} C\<^sub>1 ;; C\<^sub>2 {ret. @(R ret)}"
  using assms
  by (auto elim!:trace_to_bindE bind_RetE' simp add: hoare_rel_proc_triple_def hoare_rel_triple_def seq_itree_def kleisli_comp_def)
     (metis trace_to_Nil)+

lemma hl_proc_cond [hoare_safe]:
  assumes "H{B \<and> P} S {ret. @(Q ret)}" "H{\<not>B \<and> P} T {ret. @(Q ret)}"
  shows "H{P} if B then S else T fi {ret. @(Q ret)}"
  using assms by (simp add: hoare_rel_proc_triple_def cond_itree_def)

lemma hl_proc_seq_return [hoare_safe]:
  assumes "H{P} C {Q}"
  shows "H{P} C ;; return e {ret. \<guillemotleft>ret\<guillemotright> = e \<and> Q}"
  using assms hl_proc_seq hl_return by fastforce

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

lemma hl_output_return [hoare_safe]: 
  assumes "H{P} C ;; rdrop {Q}"
  shows "H{P} output_return C c {Q}"
  using assms
  by (auto elim!: trace_to_bindE trace_to_VisE simp add: output_return_def hoare_alt_def outp_def rdrop_def)
     (metis bind_Ret case_prod_conv kleisli_comp_def seq_itree_def trace_to_bind_left)

lemma dfp_proc_ret [wp]: "dfp (proc_ret e) = (True)\<^sub>e"
  by (force simp add: dfp_def proc_ret_def deadlock_free_Ret)

lemma dfp_output_return [wp]: "dfp (output_return P a) = dfp P"
  using deadlock_free_Ret deadlock_free_Vis 
  by (force simp add: output_return_def dfp_def outp_def deadlock_free_bind_iff)

subsection \<open> Promotion \<close>

definition promote_iproc :: "('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>1 \<Rightarrow> ('e, 'a \<times> 's\<^sub>1) itree) \<Rightarrow> 's\<^sub>2 \<Rightarrow> ('e, 'a \<times> 's\<^sub>2) itree" where
"promote_iproc a P = (\<lambda> s. if s \<in> \<S>\<^bsub>a\<^esub> then P (get\<^bsub>a\<^esub> s) \<bind> (\<lambda> (r, v). \<checkmark> (r, put\<^bsub>a\<^esub> s v)) else diverge)"

end