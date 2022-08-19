section \<open> Deadlock \<close>

theory ITree_Deadlock
  imports ITree_Divergence
begin

text \<open> Deadlock is an interaction with no visible event \<close>

definition deadlock :: "('e, 'r) itree" where
"deadlock = Vis {}\<^sub>p"

lemma stable_deadlock [simp]: "stable deadlock"
  by (simp add: deadlock_def)

lemma deadlock_trace_to: "deadlock \<midarrow>tr\<leadsto> P \<longleftrightarrow> tr = [] \<and> P = deadlock"
  by (auto simp add: deadlock_def)

lemma deadlock_bind [simp]: "deadlock \<bind> P = deadlock"
  by (metis (no_types, lifting) deadlock_def run_bind run_empty)

lemma retvals_deadlock [simp]: "\<^bold>R(deadlock) = {}"
  by (simp add: deadlock_def)

definition deadlock_free :: "('e, 'r) itree \<Rightarrow> bool" where
"deadlock_free P = (\<forall> tr. \<not> P \<midarrow>tr\<leadsto> deadlock)"

lemma pdom_empty_iff_dom_empty: "f = {\<mapsto>} \<longleftrightarrow> dom f = {}"
  by (metis pdom_res_empty pdom_res_pdom pdom_zero)

lemma empty_map_pfunD [dest!]: "{\<mapsto>} = map_pfun f F \<Longrightarrow> F = {\<mapsto>}"
  by (metis pdom_empty_iff_dom_empty pdom_map_pfun)

lemma deadlock_free_deadlock: "deadlock_free deadlock = False"
  by (simp add: deadlock_free_def deadlock_trace_to)

lemma deadlock_free_Ret: "deadlock_free (\<checkmark> x)"
  by (simp add: deadlock_def deadlock_free_def)

lemma deadlock_free_Sil: "deadlock_free (Sil P) = deadlock_free P"
  by (metis deadlock_free_def itree.disc(5) stable_deadlock trace_to_Sil trace_to_SilE)

lemma deadlock_free_bindI: "\<lbrakk> deadlock_free P; \<forall> s\<in>\<^bold>R(P). deadlock_free (Q s) \<rbrakk> \<Longrightarrow> deadlock_free (P \<bind> Q)"
  apply (auto elim!:trace_to_bindE bind_VisE' simp add: deadlock_def deadlock_free_def)
  apply (metis retvals_traceI trace_to_Nil)
  apply (meson retvals_traceI)
  done

lemma deadlock_free_bind_iff: 
  "deadlock_free (P \<bind> Q) \<longleftrightarrow> (deadlock_free P \<and> (\<forall> s\<in>\<^bold>R(P). deadlock_free (Q s)))"
  apply (auto intro: deadlock_free_bindI)
  apply (auto simp add: deadlock_free_def retvals_def)
  apply (metis deadlock_bind trace_to_bind_left)
  apply (meson trace_to_bind)
  done

end