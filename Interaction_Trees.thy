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
  Tau "('e, 'r) itree" | 
  Vis "'e \<rightharpoonup> ('e, 'r) itree"

thm itree.coinduct[simplified]

theorem itree_coind[elim, consumes 1, case_names wform Ret Tau Vis, induct pred: "HOL.eq"]:
  assumes "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Tau P \<longleftrightarrow> is_Tau Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Tau P) (Tau Q) \<Longrightarrow> \<phi> P Q" and
  "\<And> F G. \<phi> (Vis F) (Vis G) \<Longrightarrow> (dom(F) = dom(G) \<and> (\<forall> x\<in>dom(F). \<phi> (the (F x)) (the (G x))))"
  shows "P = Q"
  using assms
  by (coinduct rule: itree.coinduct, auto simp add: rel_map_iff)

theorem itree_strong_coind[elim, consumes 1, case_names wform Ret Tau Vis, induct pred: "HOL.eq"]:
  assumes phi: "\<phi> P Q" and
  "\<And> P Q. \<phi> P Q \<Longrightarrow> (is_Ret P \<longleftrightarrow> is_Ret Q) \<and> (is_Tau P \<longleftrightarrow> is_Tau Q) \<and> (is_Vis P \<longleftrightarrow> is_Vis Q)" and
  "\<And> x y. \<phi> (Ret x) (Ret y) \<Longrightarrow> x = y" and
  "\<And> P Q. \<phi> (Tau P) (Tau Q) \<Longrightarrow> \<phi> P Q \<or> P = Q" and
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
    Ret r \<Rightarrow> Tau (k r) | 
    Tau t \<Rightarrow> Tau (bind_itree t k) | 
    Vis t \<Rightarrow> Vis (\<lambda> e.
      case t e of
        None \<Rightarrow> None |
        Some x \<Rightarrow> Some (bind_itree x k)))"

friend_of_corec bind_itree :: "('e, 'r) itree \<Rightarrow> ('r \<Rightarrow> ('e, 'r) itree) \<Rightarrow> ('e, 'r) itree" where
"bind_itree u k = 
  (case u of 
    Ret r \<Rightarrow> Tau (k r) | 
    Tau t \<Rightarrow> Tau (bind_itree t k) | 
    Vis t \<Rightarrow> Vis (\<lambda> e.
      case t e of
        None \<Rightarrow> None |
        Some x \<Rightarrow> Some (bind_itree x k)))"
  by (simp add: bind_itree.code, transfer_prover)

adhoc_overloading bind bind_itree

lemma bind_Ret: "Ret v \<bind> F = Tau (F v)"
  by (simp add: bind_itree.ctr(1))

end