section \<open> Hoare Logic \<close>

theory ITree_Hoare
  imports ITree_WP
begin

text \<open> We introduce theorem attributed for safe Hoare rules and already proven triples \<close>

named_theorems hoare_safe and hoare_lemmas

definition hoare_triple :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"hoare_triple P S Q = (itree_rel S \<subseteq> spec \<top>\<^sub>S P Q)"

syntax 
  "_hoare"           :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(2H{_} /_) /{_}")
  "_hoare"           :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(2\<^bold>{_\<^bold>} /_) /\<^bold>{_\<^bold>}")
  "_preserves"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "preserves" 40)
  "_preserves_under" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ preserves _ under _" [40, 0, 40] 40)
  "_establishes"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "establishes" 40)

translations
  "_hoare P S Q" == "CONST hoare_triple (P)\<^sub>e S (Q)\<^sub>e"
  "_preserves S P" => "H{P} S {P}"
  "_preserves_under S P Q" => "H{P \<and> Q} S {P}"
  "_establishes \<sigma> P" => "H{CONST True} \<langle>\<sigma>\<rangle>\<^sub>a {P}"

lemma hoare_alt_def: "\<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>} \<longleftrightarrow> (\<forall> s s' es. P s \<and> S s \<midarrow>es\<leadsto> \<checkmark> s' \<longrightarrow> Q s')"
  by (auto simp add: hoare_triple_def spec_def itree_rel_defs retvals_def subset_iff)

lemma hoareI: "\<lbrakk> \<And> s s' es. \<lbrakk> P s; S s \<midarrow>es\<leadsto> \<checkmark> s' \<rbrakk> \<Longrightarrow> Q s' \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>}"
  by (auto simp add: hoare_alt_def)

lemma hoare_ref_by: "hoare_triple P C Q \<longleftrightarrow> (P\<^sup>< \<longrightarrow> Q\<^sup>>)\<^sub>e \<sqsubseteq> \<lbrakk>C\<rbrakk>\<^sub>p"
  by (auto simp add: hoare_triple_def itree_rel_def spec_def ref_by_fun_def ref_by_bool_def)

lemma hl_conseq:
  assumes "\<^bold>{P\<^sub>2\<^bold>} S \<^bold>{Q\<^sub>2\<^bold>}" "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`Q\<^sub>2 \<longrightarrow> Q\<^sub>1`"
  shows "\<^bold>{P\<^sub>1\<^bold>} S \<^bold>{Q\<^sub>1\<^bold>}"
  using assms by (auto simp add: hoare_alt_def, expr_auto) 

corollary hl_weaken:
  assumes "\<^bold>{P\<^sub>2\<^bold>} S \<^bold>{Q\<^bold>}" "`P\<^sub>1 \<longrightarrow> P\<^sub>2`"
  shows "\<^bold>{P\<^sub>1\<^bold>} S \<^bold>{Q\<^bold>}"
  using hl_conseq[where Q\<^sub>1="Q", OF assms] by simp

corollary hl_strengthen:
  assumes "\<^bold>{P\<^bold>} S \<^bold>{Q\<^sub>2\<^bold>}" "`Q\<^sub>2 \<longrightarrow> Q\<^sub>1`"
  shows "\<^bold>{P\<^bold>} S \<^bold>{Q\<^sub>1\<^bold>}"
  using hl_conseq[where P\<^sub>1="P", OF assms(1) _ assms(2)] by simp

corollary hl_conj_pre:
  assumes "\<^bold>{P\<^sub>1\<^bold>} S \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^sub>1 \<and> P\<^sub>2\<^bold>} S \<^bold>{Q\<^bold>}"
  by (rule hl_weaken[OF assms], simp)

corollary hl_disj_post:
  assumes "\<^bold>{P\<^bold>} S \<^bold>{Q\<^sub>1\<^bold>}"
  shows "\<^bold>{P\<^bold>} S \<^bold>{Q\<^sub>1 \<or> Q2\<^bold>}"
  by (rule hl_strengthen[OF assms], simp)

lemma hl_conj:
  assumes "\<^bold>{P\<^sub>1\<^bold>} S \<^bold>{Q\<^sub>1\<^bold>}" "\<^bold>{P\<^sub>2\<^bold>} S \<^bold>{Q\<^sub>2\<^bold>}"
  shows "\<^bold>{P\<^sub>1 \<and> P\<^sub>2\<^bold>} S \<^bold>{Q\<^sub>1 \<and> Q\<^sub>2\<^bold>}"
  using assms by (force simp add: hoare_alt_def)

lemma hl_cut:
  assumes "\<^bold>{P\<^sub>1\<^bold>} S \<^bold>{Q\<^sub>1\<^bold>}" "\<^bold>{P\<^sub>2 \<and> P\<^sub>1\<^bold>} S \<^bold>{Q\<^sub>2\<^bold>}"
  shows "\<^bold>{P\<^sub>1 \<and> P\<^sub>2\<^bold>} S \<^bold>{Q\<^sub>1 \<and> Q\<^sub>2\<^bold>}"
  using assms by (auto intro: hl_conseq hl_conj)

lemma hl_cut_inv:
  assumes "S preserves P" "S preserves Q under P"
  shows "S preserves (P \<and> Q)"
  using assms by (rule hl_cut)

lemma hl_skip: "\<^bold>{P\<^bold>} Skip \<^bold>{P\<^bold>}"
  by (auto simp add: hoare_alt_def Skip_def)

lemma hl_skip': 
  assumes "`P \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} Skip \<^bold>{Q\<^bold>}"
  using assms by (auto simp add: hoare_alt_def Skip_def, expr_simp)

lemma hl_seq: "\<lbrakk> \<^bold>{P\<^bold>} S\<^sub>1 \<^bold>{Q\<^bold>}; \<^bold>{Q\<^bold>} S\<^sub>2 \<^bold>{R\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} S\<^sub>1 ;; S\<^sub>2 \<^bold>{R\<^bold>}"
  by (auto simp add: hoare_triple_def seq_rel spec_def)

lemma hoare_seq_inv [hoare_safe]: "\<lbrakk> \<^bold>{P\<^bold>} S\<^sub>1 \<^bold>{P\<^bold>}; \<^bold>{P\<^bold>} S\<^sub>2 \<^bold>{P\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} S\<^sub>1 ;; S\<^sub>2 \<^bold>{P\<^bold>}"
  by (simp add: hl_seq)

lemma hoare_assigns: "\<^bold>{\<sigma> \<dagger> P\<^bold>} \<langle>\<sigma>\<rangle>\<^sub>a \<^bold>{P\<^bold>}"
  by (auto intro!: hoareI simp add: assigns_def, expr_simp)

lemma hl_assign: "\<^bold>{P\<lbrakk>e/x\<rbrakk>\<^bold>} x := e \<^bold>{P\<^bold>}"
  by (rule hoare_assigns)

lemma hl_assign_floyd:
  assumes "vwb_lens x"
  shows "\<^bold>{P\<^bold>} x := e \<^bold>{\<exists> x\<^sub>0 . P\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> $x = e\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>\<^bold>}"
  using assms
  by (simp add: hoare_alt_def assigns_def, expr_auto)
     (metis vwb_lens_wb wb_lens.source_stability)

lemma hoare_assigns_impl [hoare_safe]:
  assumes "`P \<longrightarrow> \<sigma> \<dagger> Q`"
  shows "\<^bold>{P\<^bold>} \<langle>\<sigma>\<rangle>\<^sub>a \<^bold>{Q\<^bold>}"
  using assms by (auto intro: hl_conseq hoare_assigns)

lemma hl_assign':
  assumes "`P \<longrightarrow> Q\<lbrakk>e/x\<rbrakk>`"
  shows "\<^bold>{P\<^bold>} x := e \<^bold>{Q\<^bold>}"
  using assms by (fact hoare_assigns_impl)

lemma hl_fwd_assign [hoare_safe]:
  assumes "vwb_lens x" "\<And> x\<^sub>0. \<^bold>{$x = e\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> P\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>\<^bold>} S \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} x := e ;; S \<^bold>{Q\<^bold>}"
  using assms
  by (auto simp add: seq_itree_def hoare_alt_def assigns_def kleisli_comp_def, expr_simp)
     (metis (no_types, lifting) mwb_lens_def vwb_lens.put_eq vwb_lens_mwb weak_lens.put_get)

lemma hl_assigns_bwd [hoare_safe]:
  assumes "H{P} S {\<sigma> \<dagger> Q}"
  shows "H{P} S ;; \<langle>\<sigma>\<rangle>\<^sub>a {Q}"
  by (blast intro: hl_seq[OF assms(1)] hoare_assigns)

lemma hl_Stop [hoare_safe]:
  "\<^bold>{P\<^bold>} Stop \<^bold>{Q\<^bold>}"
  by (simp add: hoare_alt_def)
     (meson nonterminates_iff retvals_deadlock)

lemma hl_Div [hoare_safe]:
  "\<^bold>{P\<^bold>} Div \<^bold>{Q\<^bold>}"
  by (force simp add: hoare_alt_def)

lemma hl_cond [hoare_safe]:
  assumes "\<^bold>{B \<and> P\<^bold>} S \<^bold>{Q\<^bold>}" "\<^bold>{\<not>B \<and> P\<^bold>} T \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} if B then S else T fi \<^bold>{Q\<^bold>}"
  using assms by (simp add: hoare_alt_def cond_itree_def)

lemma hl_choice [hoare_safe]:
  assumes "\<^bold>{P\<^bold>} C\<^sub>1 \<^bold>{Q\<^bold>}" "\<^bold>{P\<^bold>} C\<^sub>2 \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} C\<^sub>1 \<box> C\<^sub>2 \<^bold>{Q\<^bold>}"
  using assms
  apply (auto simp add: hoare_ref_by itree_pred_def)
  apply expr_auto
  apply (metis (mono_tags, lifting) Un_iff extchoice_fun_def in_mono retvals_extchoice)
  done

lemma hl_let [hoare_safe]:
  assumes "\<And> s. \<^bold>{P \<and> \<guillemotleft>s\<guillemotright> = \<^bold>v\<^bold>} (S (e s)) \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} let x \<leftarrow> e in S x \<^bold>{Q\<^bold>}"
  using assms by (auto simp add: hoare_alt_def let_itree_def lens_defs)

text \<open> If @{term a} is a frame for @{term C}, then we can show that any @{term I} is an invariant
  provided it only refers to variables outside of the frame. \<close>

lemma hl_frame [hoare_safe]:
  assumes "a \<sharp> (I)\<^sub>e"
  shows "\<^bold>{I\<^bold>} frame a in C \<^bold>{I\<^bold>}"
  using assms
  by (force elim: trace_to_bindE simp add: hoare_alt_def frame_def unrest_expr_def)

lemma hl_frame_rule:
  assumes "C nmods I" "H{P} C {Q}"
  shows "H{I \<and> P} C {I \<and> Q}"
  using assms by (force simp add: hoare_alt_def not_modifies_def retvals_def)

lemma hl_frame_rule_simple:
  assumes "C nmods I"
  shows "H{I} C {I}"
  using assms by (force simp add: hoare_alt_def not_modifies_def retvals_def)

lemma hl_for:
  assumes "\<And> i. i < length xs \<Longrightarrow> \<^bold>{@(R i)\<^bold>} S (xs ! i) \<^bold>{@(R (i+1))\<^bold>}"
  shows "\<^bold>{@(R 0)\<^bold>} for i in xs do S i od \<^bold>{@(R (length xs))\<^bold>}"
  using assms
proof (induct xs arbitrary: R)
  case Nil
  show ?case
    by (simp add: for_empty hl_skip del: SEXP_apply)
next
  case (Cons x xs)

  from Cons(2)[of 0] have 1: "\<^bold>{@(R 0)\<^bold>} S x \<^bold>{@(R 1)\<^bold>}"
    by (simp del: SEXP_apply)

  from Cons(1)[of "\<lambda> n. R (Suc n)"] have 2: "\<^bold>{@(R 1)\<^bold>} for_itree xs S \<^bold>{@(R (Suc (length xs)))\<^bold>}"
    by (simp del: SEXP_apply)
       (metis Cons.prems One_nat_def Suc_eq_plus1 Suc_less_eq list.size(4) nth_Cons_Suc)

  show ?case
    by (simp add: for_Cons del: SEXP_apply, meson "1" "2" hl_seq)
qed

text \<open> For loops with invariant annotations \<close>

definition for_inv :: "'i list \<Rightarrow> (nat \<Rightarrow> (bool, 's) expr) \<Rightarrow> ('i \<Rightarrow> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
[code_unfold]: "for_inv I P S = for_itree I S"

text \<open> For loops counting for m to n with invariant annotations. We use a new constant, as the form
  of invariant can be simplified in this case. \<close>

definition for_to_inv :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> (bool, 's) expr \<times> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"for_to_inv m n IC \<equiv> for_inv [m..<n+1] (\<lambda> i. fst (IC (i + m))) (\<lambda> i. snd (IC i))"

text \<open> The next code unfold law is important to ensure that invariants are not code generated, as
  they are not typically computable. \<close>

lemma for_to_inv_code [code_unfold]: "for_to_inv m n (\<lambda> i. (I i, C i)) = for_itree [m..<n+1] C"
  by (simp add: for_to_inv_def for_inv_def)

definition for_downto_inv :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> (bool, 's) expr \<times> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"for_downto_inv n m IC \<equiv> for_inv (rev [m..<n+1]) (\<lambda> i. fst (IC (n - i))) (\<lambda> i. snd (IC i))"

lemma for_downto_inv_code [code_unfold]: "for_downto_inv n m (\<lambda> i. (I i, C i)) = for_itree (rev [m..<n+1]) C"
  by (simp add: for_downto_inv_def for_inv_def)

lemma for_to_inv_empty: "n < m \<Longrightarrow> for_to_inv m n IC = Skip"
  by (simp add: for_to_inv_def for_inv_def for_empty)

syntax 
  "_for_inv_itree" :: "id \<Rightarrow> logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("for _ in _ inv _. _ do _ od")
  "_for_to_inv_itree"   :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("for _ = _ to _ inv _ do _ od")
  "_for_downto_inv_itree"   :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("for _ = _ downto _ inv _ do _ od")

translations 
  "_for_inv_itree x I i P S" == "CONST for_inv I (\<lambda> i. (P)\<^sub>e) (\<lambda> x. S)"
  "for i = m to n inv I do C od" == "CONST for_to_inv m n (\<lambda> i. ((I)\<^sub>e, C))"
  "for i = m downto n inv I do C od" == "CONST for_downto_inv m n (\<lambda> i. ((I)\<^sub>e, C))"

lemma hoare_for_inv [hoare_safe]:
  assumes "\<And> i. i < length xs \<Longrightarrow> \<^bold>{@(R i)\<^bold>} S (xs ! i) \<^bold>{@(R (i+1))\<^bold>}"
    "`P \<longrightarrow> @(R 0)`" "`@(R (length xs)) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} for x in xs inv i. @(R i) do S x od \<^bold>{Q\<^bold>}"
  unfolding for_inv_def
  by (meson assms hl_conseq hl_for)

lemma hl_for_to_inv [hoare_safe]:
  assumes "\<And>i. \<lbrakk> m \<le> i; i \<le> n \<rbrakk> \<Longrightarrow> \<^bold>{@(R i)\<^bold>} S i \<^bold>{@(R (i + 1))\<^bold>}"
   "`P \<longrightarrow> @(R m)`" "`@(R (n+1 - m+m)) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} for i = m to n inv @(R i) do S i od \<^bold>{Q\<^bold>}"
  unfolding for_to_inv_def fst_conv snd_conv
  using assms
  apply (rule_tac hoare_for_inv, simp_all only: length_upt)
  apply (metis ab_semigroup_add_class.add_ac(1) add.commute assms(1) le_add2 less_Suc_eq_le less_diff_conv nth_upt plus_1_eq_Suc)
  apply (simp add: assms(2))
  done 

lemma hl_for_downto_inv [hoare_safe]:
  assumes "\<And>i. \<lbrakk> m \<le> i; i \<le> n \<rbrakk> \<Longrightarrow> \<^bold>{@(R i)\<^bold>} S i \<^bold>{@(R (i - 1))\<^bold>}"
    "`P \<longrightarrow> @(R n)`" "`@(R (n - (Suc n - m))) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} for i = n downto m inv @(R i) do S i od \<^bold>{Q\<^bold>}"
  unfolding for_downto_inv_def fst_conv snd_conv
  apply (rule hoare_for_inv)
    apply (simp_all add: rev_nth less_diff_conv assms del: upt_Suc)
  apply (metis Nat.le_diff_conv2 add.commute add_lessD1 assms(1) diff_diff_left diff_le_self less_Suc_eq_le plus_1_eq_Suc)
  done
  
lemma hoare_while_partial [hoare_safe]:
  assumes "\<^bold>{P \<and> B\<^bold>} S \<^bold>{P\<^bold>}"
  shows "\<^bold>{P\<^bold>} while B do S od \<^bold>{\<not> B \<and> P\<^bold>}"
proof (rule hoareI)
  fix s s' tr
  assume while: "P s" "while B do S od s \<midarrow>tr\<leadsto> \<checkmark> s'"
  have B: "\<not> B s'"
    by (metis SEXP_def iterate_term_chain_iff while(2))
  have P: "P s'"
  proof (cases "B s")
    case True
    hence "(B, s) \<turnstile> S \<midarrow>tr\<leadsto>\<^sub>\<checkmark> s'"
      by (metis SEXP_def iterate_terminates_chain while(2))   
    then obtain chn s\<^sub>0 tr\<^sub>0 
      where chn: "s \<turnstile> S \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>0" "\<forall>s\<in>chain_states chn. B s" "S s\<^sub>0 \<midarrow>tr\<^sub>0\<leadsto> \<checkmark> s'" "tr = chain_trace chn @ tr\<^sub>0"
      by (metis itree_term_chain.simps)
    from assms have hl: "\<And>s s'. B s \<Longrightarrow> P s \<Longrightarrow> s' \<in> \<^bold>R (S s) \<Longrightarrow> P s'"
      by (simp add: hoare_alt_def retvals_def)
    then have chst: "\<forall>s\<in>chain_states chn. P s"
      by (rule_tac chain_invariant[where C="S" and B="B" and s="s" and s'="s\<^sub>0"])
         (simp_all add: while(1) True chn)

    have "chn \<noteq> [] \<Longrightarrow> s\<^sub>0 = snd (last chn)"
      by (metis \<open>s \<turnstile> S \<midarrow>chn\<leadsto>\<^sup>* s\<^sub>0\<close> chain_last)

    hence "P s\<^sub>0"
      by (metis chn(1) chst final_state_in_chain itree_chain.cases list.simps(3) while(1))

    thus "P s'"
      by (metis True chn(1) chn(2) chn(3) final_state_in_chain hl itree_chain.cases neq_Nil_conv retvals_traceI)
      
  next
    case False
    then show ?thesis
      using while(1) while(2) by auto
  qed
  show "\<not> B s' \<and> P s'"
    by (simp add: B P)
qed

lemmas hl_while = hoare_while_partial

text \<open> Our invariant-annotated while loop can use the state at the start of the loop in the invariant. \<close>

definition while_inv :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
[code_unfold]: "while_inv B I P = iterate B P"

definition old_expr :: "'s \<Rightarrow> ('a, 's) expr \<Rightarrow> ('a, 's) expr" where
[expr_defs]: "old_expr s e = (\<lambda> s'. e s)"

expr_constructor old_expr

syntax
  "_ghost_old" :: "id" \<comment> \<open> A distinguished name for the ghost state ("old") \<close>
  "_old_expr" :: "logic \<Rightarrow> logic" ("old[_]")
  "_while_inv_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(while _ /(2inv/ _) //do/ _ //od)")
  "_while_inv_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(while _ /(2invariant/ _) //(2do //_) //od)")

parse_translation \<open> 
  [(@{syntax_const "_ghost_old"}, fn ctx => fn term => Syntax.free "old")]\<close>

translations
  "_while_inv_itree B I P" => "CONST while_inv (B)\<^sub>e (\<lambda> _ghost_old. (I)\<^sub>e) P"
  "_while_inv_itree B I P" <= "CONST while_inv (B)\<^sub>e (\<lambda> g. (I)\<^sub>e) P"
  "_old_expr e" => "(CONST old_expr _ghost_old) (e)\<^sub>e"
  "_old_expr e" <= "CONST old_expr x (e)\<^sub>e"

lemma hl_intro_ghost:
  assumes "\<And> s. \<^bold>{\<guillemotleft>s\<guillemotright> = $\<^bold>v \<and> P\<^bold>} C \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} C \<^bold>{Q\<^bold>}"
  using assms by (auto simp add: hoare_alt_def taut_def lens_defs)

lemma hl_while_inv_ghost [hoare_safe]:
  assumes "\<And> old. \<^bold>{@(I old) \<and> B\<^bold>} S \<^bold>{@(I old)\<^bold>}" "\<And> old. `P \<and> \<guillemotleft>old\<guillemotright> = $\<^bold>v \<longrightarrow> @(I old)`" "\<And> old. `(\<not> B \<and> @(I old)) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>}while B inv @(I old) do S od\<^bold>{Q\<^bold>}"
proof -
  have 1:"\<And> old. \<^bold>{@(I old)\<^bold>}while B do S od\<^bold>{\<not> B \<and> @(I old)\<^bold>}"
    by (simp add: assms(1) hoare_while_partial while_inv_def)
  from hl_conseq[OF 1 assms(2) assms(3)] show ?thesis
    by (auto simp add: hoare_alt_def while_inv_def)
qed

lemma hl_while_inv [hoare_safe]:
  assumes "\<^bold>{I \<and> B\<^bold>} S \<^bold>{I\<^bold>}" "`P \<longrightarrow> I`" "`(\<not> B \<and> I) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>}while B inv I do S od\<^bold>{Q\<^bold>}"
  using assms by (rule_tac hl_while_inv_ghost, auto, expr_auto)

lemma hl_while_inv_init [hoare_safe]:
  assumes "\<^bold>{I \<and> B\<^bold>} S \<^bold>{I\<^bold>}" "`P \<longrightarrow> \<sigma> \<dagger> I`" "`(\<not> B \<and> I) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>}\<langle>\<sigma>\<rangle>\<^sub>a ;; while B inv I do S od\<^bold>{Q\<^bold>}"
  by (auto intro!: hl_seq[where Q="I"] hl_while_inv hoare_assigns_impl assms)

thm while_nmods

lemma while_inv_nmods [nmods]:
  "P nmods e \<Longrightarrow> while b invariant I do P od nmods e"
  by (simp add: while_inv_def while_nmods)

method hoare = ((simp add: prog_defs assigns_combine usubst usubst_eval)?, (auto intro!: hoare_safe hoare_lemmas; (simp add: usubst_eval)?))[1]

method vcg = (hoare; expr_taut?; safe?; simp?)

method hoare_auto = (hoare; expr_auto)

lemma nmods_via_hl: "P nmods e \<longleftrightarrow> (\<forall> v. H{e = \<guillemotleft>v\<guillemotright>} P {e = \<guillemotleft>v\<guillemotright>})"
  by (simp add: not_modifies_def hoare_alt_def retvals_def)

lemma nmods_hlI: "\<lbrakk> \<And> v. H{e = \<guillemotleft>v\<guillemotright>} P {e = \<guillemotleft>v\<guillemotright>} \<rbrakk> \<Longrightarrow> P nmods e"
  by (simp add: nmods_via_hl)

theorem hl_via_wlp: "\<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>} = `P \<longrightarrow> wlp S Q`"
  by (simp add: hoare_triple_def spec_def wlp_itree_def, expr_auto)

lemma hl_wlp: "`P \<longrightarrow> wlp S Q` \<Longrightarrow> \<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>}"
  by (simp add: hl_via_wlp)

method hoare_wlp uses add = (simp add: prog_defs hl_via_wlp wp usubst_eval add)
method hoare_wlp_auto uses add = (hoare_wlp add: add; expr_auto)

end