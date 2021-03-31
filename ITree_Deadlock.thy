section \<open> Deadlock \<close>

theory ITree_Deadlock
  imports ITree_Divergence
begin

text \<open> Deadlock is an interaction with no visible event \<close>

definition deadlock :: "('e, 'r) itree" where
"deadlock = Vis {\<mapsto>}"

lemma deadlock_trace_to: "deadlock \<midarrow>tr\<leadsto> P \<longleftrightarrow> tr = [] \<and> P = deadlock"
  by (auto simp add: deadlock_def)

definition deadlock_free :: "('e, 'r) itree \<Rightarrow> bool" where
"deadlock_free P = (\<forall> tr. \<not> P \<midarrow>tr\<leadsto> deadlock)"

end