theory ITree_Weak_Bisim
  imports ITree_Divergence
begin

subsection \<open> Weak Bisimulation \<close>

coinductive wbisim :: "('e, 's) itree \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" (infix "\<approx>" 50) where
wbisim_Ret [intro]: "Ret x \<approx> Ret x" |
wbisim_Sil1 [intro]: "P \<approx> Q \<Longrightarrow> Sil P \<approx> Q" |
wbisim_Sil2 [intro]: "P \<approx> Q \<Longrightarrow> P \<approx> Sil Q" |
wbisim_Vis [intro]: "\<lbrakk> dom(F) = dom(G); \<And> e. e \<in> dom(F) \<Longrightarrow> the (F e) \<approx> the (G e) \<rbrakk> \<Longrightarrow> Vis F \<approx> Vis G"

lemma Sils_eq_Vis_iff [simp]: "Sils n P = Vis F \<longleftrightarrow> (n = 0 \<and> P = Vis F)"
  by (metis Sils.simps(1) is_Vis_Sils itree.disc(9))

lemma Sils_eq_Sils_iff: "Sils n P = Sil Q \<longleftrightarrow> ((n > 0 \<and> Q = Sils (n - 1) P) \<or> (n = 0 \<and> P = Sil Q))"
  by (induct n, auto)

lemma [simp]: "Sils n P \<noteq> diverge \<longleftrightarrow> P \<noteq> diverge"
  by (metis Sils_diverge Sils_injective)

inductive_cases
  wbisim_RetE: "P \<approx> Ret x" and
  wbisim_SilE: "Sil Q \<approx> P"

lemma wbisim_sym [intro]: "P \<approx> Q \<Longrightarrow> Q \<approx> P"
  by (coinduction arbitrary: P Q, auto elim: wbisim.cases)

lemma wbisim_Sils [intro]: "Sils n P \<approx> P" 
  by (coinduction arbitrary: n P, auto, metis Sils.elims, metis Sils.elims Sils.simps(2) itree.exhaust)

thm wbisim_SilE

lemma wbisim_SilD: "Sil P \<approx> Q \<Longrightarrow> P \<approx> Q"
  apply (coinduction arbitrary: P Q, auto)
  apply (erule wbisim_SilE, auto)
  apply (smt (verit, ccfv_SIG) wbisim.cases)
  done

lemma wbisim_SilsD: "Sils n P \<approx> Q \<Longrightarrow> P \<approx> Q"
  by (induct n, auto dest: wbisim_SilD)

lemma wbisim_refl [intro]: "P \<approx> P"
  by (metis Sils.simps(1) wbisim_Sils)

lemma wbisim_trans: "\<lbrakk> P \<approx> Q; Q \<approx> R \<rbrakk> \<Longrightarrow> P \<approx> R"
  apply (coinduction arbitrary: P Q R, auto)
  oops

lemma stableE: "\<lbrakk> stable P; \<And> F. \<lbrakk> P = Vis F \<rbrakk> \<Longrightarrow> Q; \<And> x. \<lbrakk> P = Ret x \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (meson is_Ret_def is_Vis_def itree.exhaust_disc)

lemma stabilises_trace_toE: "\<lbrakk> stabilises P; \<And> F. \<lbrakk> P \<midarrow>[]\<leadsto> Vis F \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  oops

lemma "\<lbrakk> P \<approx> Q; stabilises P \<rbrakk> \<Longrightarrow> stabilises Q"
  

lemma wbisim_diverge: "P \<approx> diverge \<Longrightarrow> unstable P"
  apply (cases P rule: itree_cases, auto dest!: wbisim_SilsD)
  oops

lemma wbisim_trace_to_Nil: "P \<midarrow>[]\<leadsto> P' \<Longrightarrow> P \<approx> P'"
  by auto
  

text \<open> For CCS, weak bisimulation is not a congruence with respect to choice. Hence, Milner creates
  a derived relation, observation congruence, which adds the requirement that an initial silent
  action must be matched by a silent action in the other process. This is an issue because $\tau$
  can resolve a choice in CCS. \<close>

end