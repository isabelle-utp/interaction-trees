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

lemma hoare_skip: "\<^bold>{P\<^bold>} Skip \<^bold>{P\<^bold>}"
  by (auto simp add: hoare_alt_def Skip_def)

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
  shows "\<^bold>{P\<^bold>} if B then S else T fi \<^bold>{Q\<^bold>}"
  using assms by (simp add: hoare_alt_def cond_itree_def)

lemma hoare_seq: "\<lbrakk> \<^bold>{P\<^bold>} S\<^sub>1 \<^bold>{Q\<^bold>}; \<^bold>{Q\<^bold>} S\<^sub>2 \<^bold>{R\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} S\<^sub>1 \<Zcomp> S\<^sub>2 \<^bold>{R\<^bold>}"
  by (auto simp add: hoare_triple_def seq_rel spec_def)

lemma hoare_seq_inv [hoare_safe]: "\<lbrakk> \<^bold>{P\<^bold>} S\<^sub>1 \<^bold>{P\<^bold>}; \<^bold>{P\<^bold>} S\<^sub>2 \<^bold>{P\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} S\<^sub>1 \<Zcomp> S\<^sub>2 \<^bold>{P\<^bold>}"
  by (simp add: hoare_seq)

lemma hoare_let [hoare_safe]:
  assumes "\<And> s. \<^bold>{P \<and> \<guillemotleft>s\<guillemotright> = \<^bold>v\<^bold>} (S (e s)) \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} let x \<leftarrow> e in S x \<^bold>{Q\<^bold>}"
  using assms by (auto simp add: hoare_alt_def let_itree_def lens_defs)

lemma hoare_for:
  assumes "\<And> i. i < length xs \<Longrightarrow> \<^bold>{@(R i)\<^bold>} S (xs ! i) \<^bold>{@(R (i+1))\<^bold>}"
  shows "\<^bold>{@(R 0)\<^bold>} for i in xs do S i od \<^bold>{@(R (length xs))\<^bold>}"
  using assms
proof (induct xs arbitrary: R)
  case Nil
  show ?case
    by (simp add: for_empty hoare_skip del: SEXP_apply)
next
  case (Cons x xs)

  from Cons(2)[of 0] have 1: "\<^bold>{@(R 0)\<^bold>} S x \<^bold>{@(R 1)\<^bold>}"
    by (simp del: SEXP_apply)

  from Cons(1)[of "\<lambda> n. R (Suc n)"] have 2: "\<^bold>{@(R 1)\<^bold>} for_itree xs S \<^bold>{@(R (Suc (length xs)))\<^bold>}"
    by (simp del: SEXP_apply)
       (metis Cons.prems One_nat_def Suc_eq_plus1 Suc_less_eq list.size(4) nth_Cons_Suc)

  show ?case
    by (simp add: for_Cons del: SEXP_apply, meson "1" "2" hoare_seq)
qed

term for_itree

definition for_inv :: "'i list \<Rightarrow> (nat \<Rightarrow> (bool, 's) expr) \<Rightarrow> ('i \<Rightarrow> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"for_inv I P S = for_itree I S"

syntax "_for_inv_itree" :: "id \<Rightarrow> logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("for _ in _ inv _. _ do _ od")
translations "_for_inv_itree x I i P S" == "CONST for_inv I (\<lambda> i. (P)\<^sub>e) (\<lambda> x. S)"

lemma hoare_for_inv [hoare_safe]:
  assumes "\<And> i. i < length xs \<Longrightarrow> \<^bold>{@(R i)\<^bold>} S (xs ! i) \<^bold>{@(R (i+1))\<^bold>}"
    "`P \<longrightarrow> @(R 0)`" "`@(R (length xs)) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} for x in xs inv i. @(R i) do S x od \<^bold>{Q\<^bold>}"
  unfolding for_inv_def
  by (meson assms hoare_conseq hoare_for)

lemma hoare_while_partial [hoare_safe]:
  assumes "\<^bold>{P \<and> B\<^bold>} S \<^bold>{P\<^bold>}"
  shows "\<^bold>{P\<^bold>} while B do S od \<^bold>{\<not> B \<and> P\<^bold>}"
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