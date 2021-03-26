theory ITree_Weak_Bisim
  imports ITree_Divergence
begin

subsection \<open> Weak Bisimulation \<close>

coinductive wbisim :: "('e, 's) itree \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" (infix "\<approx>" 50) where
wbisim_Ret [intro]: "Ret x \<approx> Ret x" |
wbisim_Sil1 [intro]: "P \<approx> Q \<Longrightarrow> Sil P \<approx> Q" |
wbisim_Sil2 [intro]: "P \<approx> Q \<Longrightarrow> P \<approx> Sil Q" |
wbisim_Vis [intro]: "\<lbrakk> dom(F) = dom(G); \<And> e. e \<in> dom(F) \<Longrightarrow> the (F e) \<approx> the (G e) \<rbrakk> \<Longrightarrow> Vis F \<approx> Vis G"

inductive_cases
  wbisim_RetE: "P \<approx> Ret x"

lemma wbisim_sym [intro]: "P \<approx> Q \<Longrightarrow> Q \<approx> P"
  by (coinduction arbitrary: P Q, auto elim: wbisim.cases)

lemma "Sils n P \<approx> Sils n P"
  apply (coinduction arbitrary: n P, auto)
  oops

lemma wbisim_refl [intro]: "P = Q \<Longrightarrow> P \<approx> Q" 
  apply (coinduction arbitrary: P Q, auto)
  oops  

lemma wbisim_trans: "\<lbrakk> P \<approx> Q; Q \<approx> R \<rbrakk> \<Longrightarrow> P \<approx> R"
  apply (coinduction arbitrary: P Q R, auto)
  oops

lemma wbisim_Sils [intro]: "Sils n P \<approx> P"
  apply (induct n, auto) oops

lemma wbisim_trace_to_Nil: "P \<midarrow>[]\<leadsto> P' \<Longrightarrow> P \<approx> P'"
  oops

text \<open> For CCS, weak bisimulation is not a congruence with respect to choice. Hence, Milner creates
  a derived relation, observation congruence, which adds the requirement that an initial silent
  action must be matched by a silent action in the other process. This is an issue because $\tau$
  can resolve a choice in CCS. \<close>

end