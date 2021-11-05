section \<open> Hoare Logic \<close>

theory ITree_Hoare
  imports ITree_Relation
begin

named_theorems hoare_safe

definition hoare_triple :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"hoare_triple P S Q = (itree_rel S \<subseteq> spec \<top>\<^sub>S P Q)"

syntax 
  "_hoare" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>{_\<^bold>}/ _/ \<^bold>{_\<^bold>}")
  "_hoare" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("H{_}/ _/ {_}")
translations "_hoare P S Q" == "CONST hoare_triple (P)\<^sub>e S (Q)\<^sub>e"

lemma hoare_alt_def: "\<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>} \<longleftrightarrow> (\<forall> s s' es. P s \<and> S s \<midarrow>es\<leadsto> \<checkmark> s' \<longrightarrow> Q s')"
  by (auto simp add: hoare_triple_def spec_def itree_rel_def retvals_def subset_iff)

lemma hoareI: "\<lbrakk> \<And> s s' es. \<lbrakk> P s; S s \<midarrow>es\<leadsto> \<checkmark> s' \<rbrakk> \<Longrightarrow> Q s' \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>}"
  by (auto simp add: hoare_alt_def)

lemma hoare_conseq:
  assumes "\<^bold>{P\<^sub>2\<^bold>} S \<^bold>{Q\<^sub>2\<^bold>}" "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`Q\<^sub>2 \<longrightarrow> Q\<^sub>1`"
  shows "\<^bold>{P\<^sub>1\<^bold>} S \<^bold>{Q\<^sub>1\<^bold>}"
  using assms by (auto simp add: hoare_alt_def, expr_auto)

lemma hoare_assigns: "\<^bold>{\<sigma> \<dagger> P\<^bold>} \<langle>\<sigma>\<rangle>\<^sub>a \<^bold>{P\<^bold>}"
  by (auto intro!: hoareI simp add: assigns_def, expr_simp)

lemma hoare_assigns_impl [hoare_safe]:
  assumes "`P \<longrightarrow> \<sigma> \<dagger> Q`"
  shows "\<^bold>{P\<^bold>} \<langle>\<sigma>\<rangle>\<^sub>a \<^bold>{Q\<^bold>}"
  using assms by (auto intro: hoare_conseq hoare_assigns)

lemma hoare_fwd_assign [hoare_safe]:
  assumes "vwb_lens x" "\<And> x\<^sub>0. \<^bold>{$x = e\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> P\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>\<^bold>} S \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} x := e \<Zcomp> S \<^bold>{Q\<^bold>}"
  using assms
  by (auto simp add: hoare_alt_def assigns_def kleisli_comp_def, expr_simp)
     (metis (no_types, lifting) mwb_lens_def vwb_lens.put_eq vwb_lens_mwb weak_lens.put_get)

lemma hoare_cond [hoare_safe]:
  assumes "\<^bold>{B \<and> P\<^bold>} S \<^bold>{Q\<^bold>}" "\<^bold>{\<not>B \<and> P\<^bold>} T \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>}if B then S else T fi\<^bold>{Q\<^bold>}"
  using assms by (simp add: hoare_alt_def cond_itree_def)

lemma hoare_seq_inv [hoare_safe]: "\<lbrakk> \<^bold>{P\<^bold>} S\<^sub>1 \<^bold>{P\<^bold>}; \<^bold>{P\<^bold>} S\<^sub>2 \<^bold>{P\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} S\<^sub>1 \<Zcomp> S\<^sub>2 \<^bold>{P\<^bold>}"
  by (auto simp add: hoare_triple_def seq_rel spec_def)

(* FIXME: Correctly specify and prove the following *)

lemma hoare_for:
  assumes "\<And> m n i. \<lbrakk> m \<le> i; i < n \<rbrakk> \<Longrightarrow> \<^bold>{@(R i)\<^bold>} S i \<^bold>{@(R (i+1))\<^bold>}"
  "`P \<longrightarrow> @(R m)`" "`@(R (n - 1)) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} for i in [e\<^sub>1..<e\<^sub>2] do S i od \<^bold>{Q\<^bold>}"
  apply (simp add: hoare_triple_def itree_rel_def retvals_def for_itree_def)
  oops

lemma hoare_while_partial [hoare_safe]:
  assumes "\<^bold>{P \<and> B\<^bold>} S \<^bold>{P\<^bold>}"
  shows "\<^bold>{P\<^bold>}while B do S od\<^bold>{\<not> B \<and> P\<^bold>}"
proof (rule hoareI)
  fix s s' tr
  assume while: "P s" "while B do S od s \<midarrow>tr\<leadsto> \<checkmark> s'"
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
        hence "S s \<midarrow>fst (chn ! 0)\<leadsto> \<checkmark> (snd (chn ! 0))"
          by (metis gr_implies_not0 hd_conv_nth i ichain.chain_start length_0_conv)   
        with assms while(1) B show ?case
          by (auto simp add: hoare_alt_def)
      next
        case (Suc i)
        hence "S (snd (chn ! i)) \<midarrow>fst (chn ! Suc i)\<leadsto> \<checkmark> (snd (chn ! Suc i))"
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

definition while_inv :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
"while_inv B I P = iterate B P"

syntax "_while_inv_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("while _ inv _ do _ od")
translations "_while_inv_itree B I P" == "CONST while_inv (B)\<^sub>e (I)\<^sub>e P"

lemma hoare_while_inv_partial [hoare_safe]:
  assumes "\<^bold>{I \<and> B\<^bold>} S \<^bold>{I\<^bold>}" "`P \<longrightarrow> I`" "`(\<not> B \<and> I) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>}while B inv I do S od\<^bold>{Q\<^bold>}"
proof -
  have 1:"\<^bold>{I\<^bold>}while B inv I do S od\<^bold>{\<not> B \<and> I\<^bold>}"
    by (simp add: assms(1) hoare_while_partial while_inv_def)
  from hoare_conseq[OF 1 assms(2) assms(3)] show ?thesis by simp
qed

method hoare = (auto intro!: hoare_safe simp add: usubst_eval)

method hoare_auto = (hoare; expr_auto)

end