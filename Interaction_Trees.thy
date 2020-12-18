section \<open> Interaction Tree Semantics for CSP/Circus \<close>

theory Interaction_Trees
  imports "HOL-Library.Monad_Syntax" "HOL-Library.BNF_Corec"
begin

notation Map.empty ("[\<mapsto>]")

abbreviation "rel_map R \<equiv> rel_fun (=) (rel_option R)"

lemma rel_map_iff: 
  "rel_map R f g \<longleftrightarrow> (dom(f) = dom(g) \<and> (\<forall> x\<in>dom(f). R (the (f x)) (the (g x))))"
  apply (auto simp add: rel_fun_def)
  apply (metis not_None_eq option.rel_distinct(2))
  apply (metis not_None_eq option.rel_distinct(1))
  apply (metis option.rel_sel option.sel option.simps(3))
  apply (metis domIff option.rel_sel)
  done

codatatype ('e, 'r) itree = 
  Ret 'r | 
  Sil "('e, 'r) itree" | 
  Vis "'e \<rightharpoonup> ('e, 'r) itree"

text \<open> Small example \<close>

primcorec accept :: "'e \<Rightarrow> ('e, 's) itree"
where "accept e = Vis (\<lambda>x. if (x = e) then Some (accept e) else None)"

thm itree.coinduct[simplified]

theorem itree_coind[elim, consumes 1, case_names wform Ret Sil Vis, induct pred: "HOL.eq"]:
  assumes "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Sil P \<longleftrightarrow> is_Sil Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Sil P) (Sil Q) \<Longrightarrow> \<phi> P Q" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (dom(F) = dom(G) \<and> (\<forall> x\<in>dom(F). \<phi> (the (F x)) (the (G x))))"
  shows "P = Q"
  using assms
  by (coinduct rule: itree.coinduct, auto simp add: rel_map_iff)

theorem itree_strong_coind[elim, consumes 1, case_names wform Ret Sil Vis, induct pred: "HOL.eq"]:
  assumes phi: "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Sil P \<longleftrightarrow> is_Sil Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Sil P) (Sil Q) \<Longrightarrow> \<phi> P Q \<or> P = Q" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (dom(F) = dom(G) \<and> (\<forall> x\<in>dom(F). \<phi> (the (F x)) (the (G x)) \<or> (the (F x)) = (the (G x))))"
  shows "P = Q"
  using assms
  by (coinduct rule: itree.coinduct_strong, auto simp add: rel_map_iff)

text \<open> Up-to technique would add a functor on. Respectful closure and enhancement. 
 cf. "Coinduction all the way up". Davide Sangiorgi. Replace R \<subseteq> F(R) prove R \<subseteq> C(F(R)). \<close>

type_synonym ('e, 'r) ktree = "'r \<Rightarrow> ('e, 'r) itree"

primcorec (exhaustive) bind_itree :: "('e, 'r) itree \<Rightarrow> ('r \<Rightarrow> ('e, 's) itree) \<Rightarrow> ('e, 's) itree" where
"bind_itree u k = 
  (case u of 
    Ret r \<Rightarrow> Sil (k r) | 
    Sil t \<Rightarrow> Sil (bind_itree t k) | 
    Vis t \<Rightarrow> Vis (\<lambda> e.
      case t e of
        None \<Rightarrow> None |
        Some x \<Rightarrow> Some (bind_itree x k)))"

friend_of_corec bind_itree :: "('e, 'r) itree \<Rightarrow> ('r \<Rightarrow> ('e, 'r) itree) \<Rightarrow> ('e, 'r) itree" where
"bind_itree u k = 
  (case u of 
    Ret r \<Rightarrow> Sil (k r) | 
    Sil t \<Rightarrow> Sil (bind_itree t k) | 
    Vis t \<Rightarrow> Vis (\<lambda> e.
      case t e of
        None \<Rightarrow> None |
        Some x \<Rightarrow> Some (bind_itree x k)))"
  by (simp add: bind_itree.code, transfer_prover)

adhoc_overloading bind bind_itree

lemma bind_Ret: "Ret v \<bind> F = Sil (F v)"
  by (simp add: bind_itree.ctr(1))

text \<open> Weak Bisimulation \<close>

coinductive wbisim :: "('e, 's) itree \<Rightarrow> ('e, 's) itree \<Rightarrow> bool" (infix "\<approx>" 50) where
wbisim_sym: "P \<approx> Q \<Longrightarrow> Q \<approx> P" |
wbisim_Ret [intro]: "Ret x \<approx> Ret x" |
wbisim_Sil [intro]: "P \<approx> Q \<Longrightarrow> Sil P \<approx> Q" |
wbisim_Vis [intro]: "\<lbrakk> dom(F) = dom(G); \<And> e. e \<in> dom(F) \<Longrightarrow> the (F e) \<approx> the (G e) \<rbrakk> \<Longrightarrow> Vis F \<approx> Vis G"

lemma wbisim_refl: "P \<approx> P"
  by (coinduction arbitrary: P, auto)

lemma wbisim_trans: "\<lbrakk> P \<approx> Q; Q \<approx> R \<rbrakk> \<Longrightarrow> P \<approx> R"
  by (coinduction arbitrary: P Q R, auto intro: wbisim_sym)

text \<open> For CCS, weak bisimulation is not a congruence with respect to choice. Hence, Milner creates
  a derived relation, observation congruence, which adds the requirement that an initial silent
  action must be matched by a silent action in the other process. This is an issue because $\tau$
  can resolve a choice in CCS. \<close>

end