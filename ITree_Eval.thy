theory ITree_Eval
  imports Interaction_Trees
begin

datatype ('e, 'r) itres = VisR "'e set" | RetR 'r | RejR

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

abbreviation "MAX_SIL_STEPS \<equiv> (20::nat)"

definition "after_tr P tr = trres tr MAX_SIL_STEPS P"

definition "has_tr P tr = (trres tr MAX_SIL_STEPS P \<noteq> RejR)"

end