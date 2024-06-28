section \<open> Hoare Logic \<close>

theory ITree_Hoare
  imports ITree_WP
begin

syntax
  "_ghost_old" :: "id" \<comment> \<open> A distinguished name for the ghost state ("old") \<close>

parse_translation \<open> 
  [(@{syntax_const "_ghost_old"}, fn ctx => fn term => Syntax.free "old")]\<close>

text \<open> We introduce theorem attributed for safe Hoare rules and already proven triples \<close>

named_theorems hoare_safe and hoare_lemmas

(* Should the following be separate definitions? If they are, we can have an introduction law
  that removes the ghost state at particular points. *)

definition hoare_rel_triple :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" where
"hoare_rel_triple P C Q = (\<forall> s s' es. P s \<and> C s \<midarrow>es\<leadsto> \<checkmark> s' \<longrightarrow> Q s s')"

abbreviation hoare_triple :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"hoare_triple P C Q \<equiv> hoare_rel_triple P C (\<lambda> x. Q)"

lemma hoare_triple_def: "hoare_triple P S Q = (itree_rel S \<subseteq> spec \<top>\<^sub>S P Q)"
  by (auto simp add: hoare_rel_triple_def itree_rel_def spec_def itree_pred_def retvals_def)

syntax 
  "_hoare"           :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(2H{_} /_) /{_}")
  "_hoare"           :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(2\<^bold>{_\<^bold>} /_) /\<^bold>{_\<^bold>}")
  "_preserves"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "preserves" 40)
  "_preserves_under" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ preserves _ under _" [40, 0, 40] 40)
  "_establishes"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "establishes" 40)

translations
  "H{P} C {Q}" => "CONST hoare_rel_triple (P)\<^sub>e C (\<lambda> _ghost_old. (Q)\<^sub>e)" 
  "H{P} C {Q}" <= "CONST hoare_triple (P)\<^sub>e C (Q)\<^sub>e"
  "_preserves S P" => "H{P} S {P}"
  "_preserves_under S P Q" => "H{P \<and> Q} S {P}"
  "_establishes \<sigma> P" => "H{CONST True} \<langle>\<sigma>\<rangle>\<^sub>a {P}"

lemma hoare_alt_def: "\<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>} \<longleftrightarrow> (\<forall> s s' es. P s \<and> S s \<midarrow>es\<leadsto> \<checkmark> s' \<longrightarrow> Q s')"
  by (auto simp add: hoare_triple_def spec_def itree_rel_defs retvals_def subset_iff)

lemma hoareI: "\<lbrakk> \<And> s s' es. \<lbrakk> P s; S s \<midarrow>es\<leadsto> \<checkmark> s' \<rbrakk> \<Longrightarrow> Q s' \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} S \<^bold>{Q\<^bold>}"
  by (auto simp add: hoare_alt_def)

lemma hoare_ref_by: "hoare_triple P C Q \<longleftrightarrow> (P\<^sup>< \<longrightarrow> Q\<^sup>>)\<^sub>e \<sqsubseteq> \<lbrakk>C\<rbrakk>\<^sub>p"
  by (auto simp add: hoare_triple_def itree_rel_def spec_def ref_by_fun_def ref_by_bool_def)

lemma hl_prestate:
  assumes "\<And> old. \<^bold>{\<guillemotleft>old\<guillemotright> = \<^bold>v \<and> P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk>\<^bold>} C \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} C \<^bold>{Q\<^bold>}"
  using assms by (simp add: hoare_alt_def lens_defs, expr_auto)

text \<open> We can remove the ghost prestate by adding a ghost state variable to the precondition \<close>

lemma hl_ghost_state_old:
  assumes "\<And> s\<^sub>0. H{P \<and> \<guillemotleft>s\<^sub>0\<guillemotright> = \<^bold>v} C {Q(\<guillemotleft>s\<^sub>0\<guillemotright>)}" 
  shows "H{P} C {Q(\<guillemotleft>old\<guillemotright>)}"
  using assms
  by (auto simp add: hoare_rel_triple_def lens_defs)

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

lemma hl_fwd_assign_mwb [hoare_safe]:
  assumes "mwb_lens x" "\<And> x\<^sub>0. \<^bold>{\<^bold>D(x) \<and> $x = e\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> P\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>\<^bold>} S \<^bold>{Q\<^bold>}" "`P \<longrightarrow> \<^bold>D(x)`"
  shows "\<^bold>{P\<^bold>} x := e ;; S \<^bold>{Q\<^bold>}"
  using assms
  by (auto simp add: seq_itree_def hoare_alt_def assigns_def kleisli_comp_def, expr_simp)
     (metis (no_types, opaque_lifting) mwb_lens.put_put mwb_lens.weak_get_put mwb_lens_weak weak_lens.put_closure weak_lens.put_get)

lemma hl_fwd_assign:
  assumes "vwb_lens x" "\<And> x\<^sub>0. \<^bold>{$x = e\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> P\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>\<^bold>} S \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} x := e ;; S \<^bold>{Q\<^bold>}"
  by (simp add: hl_fwd_assign_mwb assms)

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

lemma hl_guard [hoare_safe]:
  assumes "\<^bold>{P \<and> Q\<^bold>} C \<^bold>{R\<^bold>}"
  shows "\<^bold>{P\<^bold>} \<exclamdown>Q! ;; C \<^bold>{R\<^bold>}"
  using assms
  by (auto simp add: hoare_alt_def test_def seq_itree_def kleisli_comp_def)
     (meson nonterminates_iff retvals_deadlock)

lemma hl_match [hoare_safe]:
  assumes "\<And> v. \<^bold>{\<guillemotleft>v\<guillemotright> = e \<and> P\<^bold>} C(v) \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} match_itree (e)\<^sub>e C \<^bold>{Q\<^bold>}"
  using assms by (simp add: match_itree_def hoare_alt_def)

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

lemma hl_frame_rule':
  assumes "C nmods I" "H{I \<and> P} C {Q}"
  shows "H{I \<and> P} C {I \<and> Q}"
  using assms by (force simp add: hoare_alt_def not_modifies_def retvals_def)

lemma hl_frame_rule_simple:
  assumes "C nmods I"
  shows "H{I} C {I}"
  using assms by (force simp add: hoare_alt_def not_modifies_def retvals_def)

lemma hl_for:
  assumes "\<And> i. i < length xs \<Longrightarrow> \<^bold>{@(R i)\<^bold>} S (xs ! i) \<^bold>{@(R (i+1))\<^bold>}"
  shows "\<^bold>{@(R 0)\<^bold>} for i in \<guillemotleft>xs\<guillemotright> do S i od \<^bold>{@(R (length xs))\<^bold>}"
  using assms
proof (induct xs arbitrary: R)
  case Nil
  show ?case
    by (metis SEXP_def for_empty hl_skip list.size(3))
next
  case (Cons x xs)

  from Cons(2)[of 0] have 1: "\<^bold>{@(R 0)\<^bold>} S x \<^bold>{@(R 1)\<^bold>}"
    by (simp del: SEXP_apply)

  from Cons(1)[of "\<lambda> n. R (Suc n)"] have 2: "\<^bold>{@(R 1)\<^bold>} for_itree (\<guillemotleft>xs\<guillemotright>)\<^sub>e S \<^bold>{@(R (Suc (length xs)))\<^bold>}"
    by (simp del: SEXP_apply)
       (metis Cons.prems One_nat_def Suc_eq_plus1 Suc_less_eq list.size(4) nth_Cons_Suc)

  show ?case
    by (simp add: for_Cons del: SEXP_apply) (metis "1" "2" SEXP_def hl_seq)
qed

text \<open> A more general version of the for-loop law where the invariant can depend on the initial
       state, and the list to iterate over can be an expression (evaluated on the initial state). \<close>

lemma hl_for_prestate:
  \<comment> \<open> The notation @{term "P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk>"} means the @{term P} holds on the initial state @{term s\<^sub>0}. \<close>
  assumes 
    "\<And> s\<^sub>0 i. i < length (xs s\<^sub>0) \<Longrightarrow> \<^bold>{@(R s\<^sub>0 i)\<^bold>} S (xs s\<^sub>0 ! i) \<^bold>{@(R s\<^sub>0 (i+1))\<^bold>}"
    "\<And> s\<^sub>0. `P \<and> \<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<longrightarrow> @(R s\<^sub>0 0)`"
    "\<And> s\<^sub>0. `@(R s\<^sub>0 (length (xs s\<^sub>0))) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} for i in xs do S i od \<^bold>{Q\<^bold>}"
proof (rule_tac hl_prestate)
  fix s\<^sub>0
  show "\<^bold>{\<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk>\<^bold>} for i in xs do S i od \<^bold>{Q\<^bold>}"
  proof -
    have "\<And> i. i < length (xs s\<^sub>0) \<Longrightarrow> \<^bold>{P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(R s\<^sub>0 i)\<^bold>} S (xs s\<^sub>0 ! i) \<^bold>{P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(R s\<^sub>0 (i + 1))\<^bold>}"
    proof (simp, rule hl_frame_rule')
      fix i
      assume i: "i < length (xs s\<^sub>0)"
      show "S (xs s\<^sub>0 ! i) nmods P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk>"
        by (expr_simp add: not_modifies_def)
      from assms(1) i show "\<^bold>{P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(R s\<^sub>0 i)\<^bold>} S (xs s\<^sub>0 ! i) \<^bold>{@(R s\<^sub>0 (Suc i))\<^bold>}"
        by (force simp add: hoare_alt_def)
    qed
    hence w:"\<^bold>{P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(R s\<^sub>0 0)\<^bold>} for i in \<guillemotleft>xs s\<^sub>0\<guillemotright> do S i od \<^bold>{P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(R s\<^sub>0 (length (xs s\<^sub>0)))\<^bold>}"
      by (rule hl_for, simp)
    from assms(2-3) have "\<^bold>{\<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk>\<^bold>} for i in \<guillemotleft>xs s\<^sub>0\<guillemotright> do S i od \<^bold>{Q\<^bold>}"
      by (rule_tac hl_conseq[OF w]; expr_auto)
    thus ?thesis
      by (auto simp add: for_itree_def hoare_alt_def, expr_auto)
  qed
qed

text \<open> For loops with invariant annotations \<close>

definition for_inv :: "('s \<Rightarrow> 'i list) \<Rightarrow> ('s \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('i \<Rightarrow> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
[code_unfold]: "for_inv I P S = for_itree I S"

text \<open> For loops counting for m to n with invariant annotations. We use a new constant, as the form
  of invariant can be simplified in this case. \<close>

definition for_to_inv :: "('s \<Rightarrow> nat) \<Rightarrow> ('s \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<times> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"for_to_inv m n IC \<equiv> for_itree (SEXP (\<lambda> s. [(m s)..<(n s)+1])) (\<lambda> i. snd (IC i))"

text \<open> The next code unfold law is important to ensure that invariants are not code generated, as
  they are not typically computable. \<close>

lemma for_to_inv_code [code_unfold]: "for_to_inv m n (\<lambda> i. (I i, C i)) = for_itree (\<lambda> s. [m s..<n s+1]) C"
  by (simp add: for_to_inv_def for_inv_def SEXP_def)

definition for_downto_inv :: "('s \<Rightarrow> nat) \<Rightarrow> ('s \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<times> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"for_downto_inv n m IC \<equiv> for_itree (SEXP (\<lambda> s. rev [m s..<n s+1])) (\<lambda> i. snd (IC i))"

lemma for_downto_inv_code [code_unfold]: "for_downto_inv n m (\<lambda> i. (I i, C i)) = for_itree (\<lambda> s. rev [m s..<n s+1]) C"
  by (simp add: for_downto_inv_def for_inv_def SEXP_def)

lemma for_to_inv_empty: "n < m \<Longrightarrow> for_to_inv (\<guillemotleft>m\<guillemotright>)\<^sub>e (\<guillemotleft>n\<guillemotright>)\<^sub>e IC = Skip"
  by (simp add: for_to_inv_def for_inv_def, metis for_empty)

syntax 
  "_for_inv_itree" :: "id \<Rightarrow> logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("for _ in _ inv _. _ do _ od")
  "_for_to_inv_itree"   :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("for _ = _ to _ inv _ do _ od")
  "_for_downto_inv_itree"   :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("for _ = _ downto _ inv _ do _ od")

translations 
  "_for_inv_itree x I i P S" => "CONST for_inv (I)\<^sub>e (\<lambda> _ghost_old i. (P)\<^sub>e) (\<lambda> x. S)"
  "_for_inv_itree x I i P S" <= "CONST for_inv (I)\<^sub>e (\<lambda> old i. (P)\<^sub>e) (\<lambda> x. S)"
  "for i = m to n inv I do C od" => "CONST for_to_inv (m)\<^sub>e (n)\<^sub>e (\<lambda> i. (\<lambda> _ghost_old. (I)\<^sub>e, C))"
  "for i = m to n inv I do C od" <= "CONST for_to_inv (m)\<^sub>e (n)\<^sub>e (\<lambda> i. (\<lambda> old. (I)\<^sub>e, C))"
  "for i = m downto n inv I do C od" => "CONST for_downto_inv (m)\<^sub>e (n)\<^sub>e (\<lambda> i. (\<lambda> _ghost_old. (I)\<^sub>e, C))"
  "for i = m downto n inv I do C od" <= "CONST for_downto_inv (m)\<^sub>e (n)\<^sub>e (\<lambda> i. (\<lambda> old. (I)\<^sub>e, C))"

lemma hoare_for_inv_lit :
  assumes "\<And> i. i < length xs \<Longrightarrow> \<^bold>{@(R i)\<^bold>} S (xs ! i) \<^bold>{@(R (i+1))\<^bold>}"
    "`P \<longrightarrow> @(R 0)`" "`@(R (length xs)) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} for x in \<guillemotleft>xs\<guillemotright> inv i. @(R i) do S x od \<^bold>{Q\<^bold>}"
  unfolding for_inv_def
  by (auto intro: hl_conseq hl_for assms)

lemma hoare_for_intro_ghost:
  assumes "\<And> xs. \<^bold>{P \<and> \<guillemotleft>xs\<guillemotright> = e\<^bold>} for x in \<guillemotleft>xs\<guillemotright> inv i. @(R i) do S x od \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} for x in e inv i. @(R i) do S x od \<^bold>{Q\<^bold>}"
  using assms
  unfolding for_inv_def for_itree_def hoare_alt_def by auto

lemma hoare_for_inv [hoare_safe]:
  \<comment> \<open> The notation @{term "P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk>"} means the @{term P} holds on the initial state @{term s\<^sub>0}. \<close>
  assumes 
    "\<And> s\<^sub>0 i. i < length (xs s\<^sub>0) \<Longrightarrow> \<^bold>{@(R s\<^sub>0 i)\<^bold>} S (xs s\<^sub>0 ! i) \<^bold>{@(R s\<^sub>0 (i+1))\<^bold>}"
    "\<And> s\<^sub>0. `P \<and> \<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<longrightarrow> @(R s\<^sub>0 0)`"
    "\<And> s\<^sub>0. `@(R s\<^sub>0 (length (xs s\<^sub>0))) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} for i in xs inv i. @(R old i) do S i od \<^bold>{Q\<^bold>}"
  unfolding for_inv_def
  by (rule hl_for_prestate[OF assms], simp)

lemma hl_for_to_inv [hoare_safe]:
  assumes
    "\<And>s\<^sub>0 i. \<lbrakk> m s\<^sub>0 \<le> i; i \<le> n s\<^sub>0 \<rbrakk> \<Longrightarrow> \<^bold>{@(R s\<^sub>0 i)\<^bold>} S i \<^bold>{@(R s\<^sub>0 (i + 1))\<^bold>}"
    "\<And> s\<^sub>0. `P \<longrightarrow> @(R s\<^sub>0 (m s\<^sub>0))`" "\<And> s\<^sub>0. `@(R s\<^sub>0 (n s\<^sub>0+1 - m s\<^sub>0 + m s\<^sub>0)) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} for i = m to n inv @(R old i) do S i od \<^bold>{Q\<^bold>}"
  unfolding for_to_inv_def
proof (rule_tac hl_for_prestate[where R="\<lambda> s\<^sub>0 i. R s\<^sub>0 (i + m s\<^sub>0)"], simp_all only: length_upt snd_conv nth_upt SEXP_apply, simp)
  fix s\<^sub>0 i
  assume i: "i < Suc (n s\<^sub>0) - m s\<^sub>0"
  with assms(1)[of "s\<^sub>0" "i + m s\<^sub>0"]
  show "\<^bold>{@(R s\<^sub>0 (i + m s\<^sub>0))\<^bold>} S (m s\<^sub>0 + i) \<^bold>{@(R s\<^sub>0 (Suc (i + m s\<^sub>0)))\<^bold>}"
    by (simp add: add.commute less_diff_conv)
next
  fix s\<^sub>0
  from assms(2) show "`P \<and> \<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<longrightarrow> @(R s\<^sub>0 (0 + m s\<^sub>0))`"
    by expr_simp
  from assms(3) show "`@(R s\<^sub>0 (n s\<^sub>0 + 1 - m s\<^sub>0 + m s\<^sub>0)) \<longrightarrow> Q`"
    by expr_simp
qed

lemma hl_for_downto_inv [hoare_safe]:
  assumes "\<And> s\<^sub>0 i. \<lbrakk> m s\<^sub>0 \<le> i; i \<le> n s\<^sub>0 \<rbrakk> \<Longrightarrow> \<^bold>{@(R s\<^sub>0 i)\<^bold>} S i \<^bold>{@(R s\<^sub>0 (i - 1))\<^bold>}"
    "\<And> s\<^sub>0. `P \<longrightarrow> @(R s\<^sub>0 (n s\<^sub>0))`" "\<And> s\<^sub>0. `@(R s\<^sub>0 ((n s\<^sub>0) - (Suc (n s\<^sub>0) - (m s\<^sub>0)))) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} for i = n downto m inv @(R old i) do S i od \<^bold>{Q\<^bold>}"
  unfolding for_downto_inv_def
proof (rule_tac hl_for_prestate[where R="\<lambda> s\<^sub>0 i. R s\<^sub>0 (n s\<^sub>0 - i)"], simp_all only: length_upt snd_conv nth_upt SEXP_apply)
  fix s\<^sub>0 i
  assume i: "i < length (rev [m s\<^sub>0..<n s\<^sub>0 + 1])"
  show "\<^bold>{@(R s\<^sub>0 (n s\<^sub>0 - i))\<^bold>} S (rev [m s\<^sub>0..<n s\<^sub>0 + 1] ! i) \<^bold>{@(R s\<^sub>0 (n s\<^sub>0 - (i + 1)))\<^bold>}"
  proof (cases "m s\<^sub>0 < n s\<^sub>0")
    case True
    with i assms(1)[of "s\<^sub>0" "n s\<^sub>0 - i", simplified] show ?thesis
      by (case_tac "i = 0", simp_all add: rev_nth)
  next
    case False
    with i assms(1)[of "s\<^sub>0" "n s\<^sub>0 - i", simplified] show ?thesis
      by auto
  qed
next
  fix s\<^sub>0
  from assms(2) show "`P \<and> \<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<longrightarrow> @(R s\<^sub>0 (n s\<^sub>0 - 0))`" by expr_simp
  from assms(3) show "`@(R s\<^sub>0 (n s\<^sub>0 - length (rev [m s\<^sub>0..<n s\<^sub>0 + 1]))) \<longrightarrow> Q`"
    by expr_auto ( metis One_nat_def Suc_diff_le add.commute diff_diff_cancel diff_diff_left plus_1_eq_Suc
                  , metis diff_diff_cancel diff_is_0_eq' le_common_total not_less_eq_eq)
qed

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
  "_old_expr" :: "logic \<Rightarrow> logic" ("old[_]")
  "_while_inv_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(while _ /(2inv/ _) //do/ _ //od)")
  "_while_inv_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(while _ /(2invariant/ _) //(2do //_) //od)")

translations
  "_while_inv_itree B I P" => "CONST while_inv (B)\<^sub>e (\<lambda> _ghost_old. (I)\<^sub>e) P"
  "_while_inv_itree B I P" <= "CONST while_inv (B)\<^sub>e (\<lambda> g. (I)\<^sub>e) P"
  "_old_expr e" => "(CONST old_expr _ghost_old) (e)\<^sub>e"
  "_old_expr e" <= "CONST old_expr x (e)\<^sub>e"

lemma hl_intro_ghost:
  assumes "\<And> s. \<^bold>{\<guillemotleft>s\<guillemotright> = $\<^bold>v \<and> P\<^bold>} C \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} C \<^bold>{Q\<^bold>}"
  using assms by (auto simp add: hoare_alt_def taut_def lens_defs)

(*
lemma hl_while_inv_ghost [hoare_safe]:
  assumes "\<And> old. \<^bold>{@(I old) \<and> B\<^bold>} S \<^bold>{@(I old)\<^bold>}" "\<And> old. `P \<and> \<guillemotleft>old\<guillemotright> = $\<^bold>v \<longrightarrow> @(I old)`" "\<And> old. `(\<not> B \<and> @(I old)) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>}while B inv @(I old) do S od\<^bold>{Q\<^bold>}"
proof -
  have 1:"\<And> old. \<^bold>{@(I old)\<^bold>}while B do S od\<^bold>{\<not> B \<and> @(I old)\<^bold>}"
    by (simp add: assms(1) hoare_while_partial while_inv_def)
  from hl_conseq[OF 1 assms(2) assms(3)] show ?thesis
    by (auto simp add: hoare_alt_def while_inv_def)
qed
*)

text \<open> The following law generalises the while law in several ways:
       (1) the invariant may refer to the initial state of the loop via "old";
       (2) the precondition holding on the initial state may be used in the invariant proof;
       (3) it can also be used in both the implications. 
       As a result, this law allows better support for invariant framing. \<close>

lemma hl_while_inv_prestate [hoare_safe]:
  assumes 
    \<comment> \<open> The notation @{term "P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk>"} means the @{term P} holds on the initial state @{term s\<^sub>0}. \<close>
    "\<And> s\<^sub>0. \<^bold>{P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I s\<^sub>0) \<and> B\<^bold>} S \<^bold>{@(I s\<^sub>0)\<^bold>}" 
    "\<And> s\<^sub>0. `P \<and> \<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<longrightarrow> @(I s\<^sub>0)`" 
    "\<And> s\<^sub>0. `(P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> \<not> B \<and> @(I s\<^sub>0)) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>}while B inv @(I old) do S od\<^bold>{Q\<^bold>}"
proof (rule_tac hl_prestate)
  fix s\<^sub>0
  show "\<^bold>{\<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk>\<^bold>} while B inv @(I old) do S od \<^bold>{Q\<^bold>}"
  proof -
    have "\<^bold>{(P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I s\<^sub>0)) \<and> B\<^bold>} S \<^bold>{P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I s\<^sub>0)\<^bold>}"
    proof (simp, rule hl_frame_rule')
      show "S nmods P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk>"
        by (expr_simp add: not_modifies_def)
      show "\<^bold>{P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I s\<^sub>0) \<and> B\<^bold>} S \<^bold>{@(I s\<^sub>0)\<^bold>}"
        by (fact assms(1))
    qed
    hence w:"\<^bold>{P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I s\<^sub>0)\<^bold>} while B do S od \<^bold>{\<not> B \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I s\<^sub>0)\<^bold>}"
      by (simp add: hoare_while_partial)
    from assms(2-3) show ?thesis
      unfolding while_inv_def
      by (rule_tac hl_conseq[OF w]; expr_auto)
  qed
qed

lemma hl_while_inv [hoare_safe]:
  assumes "\<^bold>{I \<and> B\<^bold>} S \<^bold>{I\<^bold>}" "`P \<longrightarrow> I`" "`(\<not> B \<and> I) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>}while B inv I do S od\<^bold>{Q\<^bold>}"
proof (rule hl_while_inv_prestate)
  fix old
  from assms(1) show "\<^bold>{P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> I \<and> B\<^bold>} S \<^bold>{I\<^bold>}"
    by (rule hl_conseq; simp)
  from assms(2) show "`P \<and> \<guillemotleft>old\<guillemotright> = $\<^bold>v \<longrightarrow> I`"
    by (expr_simp)
  from assms(3) show "`P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> \<not> B \<and> I \<longrightarrow> Q`"
    by (expr_simp)
qed

lemma hl_while_inv_init [hoare_safe]:
  assumes "\<^bold>{I \<and> B\<^bold>} S \<^bold>{I\<^bold>}" "`P \<longrightarrow> \<sigma> \<dagger> I`" "`(\<not> B \<and> I) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>}\<langle>\<sigma>\<rangle>\<^sub>a ;; while B inv I do S od\<^bold>{Q\<^bold>}"
  by (auto intro!: hl_seq[where Q="I"] hl_while_inv hoare_assigns_impl assms)

lemma while_inv_nmods [nmods]:
  "P nmods e \<Longrightarrow> while b invariant I do P od nmods e"
  by (simp add: while_inv_def while_nmods)

method hoare = ((simp add: prog_defs z_defs z_locale_defs assigns_combine usubst usubst_eval)?, (auto intro!: hoare_safe hoare_lemmas; (simp add: usubst_eval)?))[1]

text \<open> Verification condition generation \<close>

method vcg_lens = (hoare; expr_lens_taut?; safe?; simp?) \<comment> \<open> Most useful when multiple states are present \<close>

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