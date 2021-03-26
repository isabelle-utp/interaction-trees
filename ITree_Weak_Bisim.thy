theory ITree_Weak_Bisim
  imports ITree_Divergence
begin

subsection \<open> Weak Bisimulation \<close>

inductive wbisim_upto :: "('e, 's) itree \<Rightarrow> (('e, 's) itree \<Rightarrow> ('e, 's) itree \<Rightarrow> bool) \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" (infix "\<approx>\<^bsub>_\<^esub>" 50) where
wbupto_Ret [intro]: "Ret x \<approx>\<^bsub>R\<^esub> Ret x" |
wbupto_Sil1 [intro]: "P \<approx>\<^bsub>R\<^esub> Q \<Longrightarrow> Sil P \<approx>\<^bsub>R\<^esub> Q" |
wbupto_Sil2 [intro]: "P \<approx>\<^bsub>R\<^esub> Q \<Longrightarrow> P \<approx>\<^bsub>R\<^esub> Sil Q" |
wbisim_Vis [intro]: "\<lbrakk> dom(F) = dom(G); \<And> e. e \<in> dom(F) \<Longrightarrow> R (the (F e)) (the (G e)) \<rbrakk> \<Longrightarrow> Vis F \<approx>\<^bsub>R\<^esub> Vis G"

abbreviation (input) "wbupto R \<equiv> (\<lambda> P Q. P \<approx>\<^bsub>R\<^esub> Q)"

lemma monotonic_wbisim_upto: "P \<approx>\<^bsub>R\<^esub> Q \<Longrightarrow> R \<le> S \<Longrightarrow> P \<approx>\<^bsub>S\<^esub> Q"
  by (induct rule: wbisim_upto.induct ,auto)

lemma mono_stabilises_to [mono add]: "R \<le> S \<Longrightarrow> wbupto R \<le> wbupto S"
  by (auto intro: monotonic_wbisim_upto)

coinductive wbisim :: "('e, 's) itree \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" (infix "\<approx>" 50) where
wbisim: "P \<approx>\<^bsub>wbisim\<^esub> Q \<Longrightarrow> P \<approx> Q"

inductive_cases
  wbisim_RetE: "P \<approx> Ret x"

lemma wbisim_sym [intro]: "P \<approx> Q \<Longrightarrow> Q \<approx> P"
  apply (coinduction arbitrary: P Q, auto) oops

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