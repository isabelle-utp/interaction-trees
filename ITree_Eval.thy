theory ITree_Eval
  imports Interaction_Trees
begin

datatype ('e, 'r) itres = VisR "'e set" | RetR 'r | RejR

fun has_trace :: "'e list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('e, 's) itree \<Rightarrow> ('e, 's) itres" where
"has_trace tr n mx (Ret x) = RetR x" |
"has_trace tr (Suc n) mx (Sil P) = has_trace tr n mx P" |
"has_trace tr 0 mx (Sil P) = RejR" |
"has_trace (e # tr) n mx (Vis F) = (if e \<in> pdom F then has_trace tr mx mx (F e) else RejR)" |
"has_trace [] n mx (Vis F) = VisR (pdom F)"

end