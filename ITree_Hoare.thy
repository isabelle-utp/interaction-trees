section \<open> Hoare Logic \<close>

theory ITree_Hoare
  imports ITree_Relation
begin

definition hoare_triple :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"hoare_triple P S Q = (itree_rel S \<subseteq> spec \<top>\<^sub>S P Q)"

syntax "_hoare" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>{_\<^bold>} _ \<^bold>{_\<^bold>}")
translations "_hoare P S Q" == "CONST hoare_triple (P)\<^sub>e S (Q)\<^sub>e"

lemma hoare_alt_def: "\<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>} \<longleftrightarrow> (\<forall> s s' es. P s \<and> S s \<midarrow>es\<leadsto> Ret s' \<longrightarrow> Q s')"
  by (auto simp add: hoare_triple_def spec_def itree_rel_def retvals_def subset_iff)

lemma hoareI: "\<lbrakk> \<And> s s' es. \<lbrakk> P s; S s \<midarrow>es\<leadsto> Ret s' \<rbrakk> \<Longrightarrow> Q s' \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>}"
  by (auto simp add: hoare_alt_def)

lemma hoare_while_partial:
  assumes "\<^bold>{P \<and> B\<^bold>} S \<^bold>{P\<^bold>}"
  shows "\<^bold>{P\<^bold>}while B do S od\<^bold>{\<not> B \<and> P\<^bold>}"
proof (rule hoareI)
  fix s s' tr
  assume while: "P s" "while B do S od s \<midarrow>tr\<leadsto> \<cmark> s'"
  show "\<not> B s' \<and> P s'"
  proof (cases "B s")
    case True
    note B = this
    obtain chn where chn: "itree_chain S s s' chn" "concat (map fst chn) = tr" "\<forall> i < length chn - 1. B (snd (chn ! i))" "\<not> B s'"
      by (metis SEXP_def True iterate_term_chain while(2))
    then interpret ichain: itree_chain S s s' chn by simp
    have "\<forall> i < length chn. P (snd (chn ! i))"
    proof (clarify)
      fix i
      assume i: "i < length chn"
      thus "P (snd (chn ! i))"
      proof (induct i)
        case 0
        hence "S s \<midarrow>fst (chn ! 0)\<leadsto> \<cmark> (snd (chn ! 0))"
          by (metis gr_implies_not0 hd_conv_nth i ichain.chain_start length_0_conv)   
        with assms while(1) B show ?case
          by (auto simp add: hoare_alt_def)
      next
        case (Suc i)
        hence "S (snd (chn ! i)) \<midarrow>fst (chn ! Suc i)\<leadsto> \<cmark> (snd (chn ! Suc i))"
          by (metis Suc_eq_plus1 ichain.chain_iter less_diff_conv)
        moreover have "B (snd (chn ! i))"
          by (metis Suc.prems Suc_lessE chn(3) diff_Suc_1)
        moreover have "P (snd (chn ! i))"
          by (simp add: Suc.hyps Suc.prems Suc_lessD)
        ultimately show ?case
          using assms by (auto simp add: hoare_alt_def)
      qed
    qed
    thus ?thesis
      by (metis Suc_diff_1 chn(4) ichain.last_st ichain.length_chain last_conv_nth length_greater_0_conv lessI)
  next
    case False
    then show ?thesis
      using while(1) while(2) by force 
  qed
qed

end