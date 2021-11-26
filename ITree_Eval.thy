subsection \<open> Evaluating ITrees \<close>

theory ITree_Eval
  imports Interaction_Trees
begin

text \<open> The following type encodes the possible results obtained from a given event trace. \<close>

datatype ('e, 'r) itres = 
  VisR "'e set" \<comment> \<open> Accept trace, present a choice \<close>
  | RetR 'r \<comment> \<open> Accept trace, return a value \<close>
  | RejR \<comment> \<open> Reject trace \<close>

text \<open> The next function allows to calculate the result of a given trace. The number of permitted
  internal events is bounded to ensure that the function terminates. \<close>

fun trres' :: "'e list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('e, 's) itree \<Rightarrow> ('e, 's) itres" where
"trres' tr n mx (Ret x) = RetR x" |
"trres' tr (Suc n) mx (Sil P) = trres' tr n mx P" |
"trres' tr 0 mx (Sil P) = RejR" |
"trres' (e # tr) n mx (Vis F) = (if e \<in> pdom F then trres' tr mx mx (F e) else RejR)" |
"trres' [] n mx (Vis F) = VisR (pdom F)"

abbreviation "trres tr n P \<equiv> trres' tr n n P"

lemma trres_Sils:
  "m \<le> n \<Longrightarrow> trres tr n (Sils m P) = trres' tr (n - m) n P"
  by (induct m arbitrary: n tr P, auto)
     (metis Sils_Sil_shift Suc_diff_le Suc_leD Suc_le_D diff_Suc_Suc trres'.simps(2))

text \<open> We fix this as a constant, which can be instantiated later. \<close>

consts MAX_SIL_STEPS :: nat

definition "after_tr P tr = trres tr MAX_SIL_STEPS P"

definition "has_tr P tr = (trres tr MAX_SIL_STEPS P \<noteq> RejR)"

end