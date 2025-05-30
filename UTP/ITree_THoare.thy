section \<open> Total Correctness Hoare Logic \<close>

theory ITree_THoare
  imports ITree_Hoare
begin

text \<open> Total correctness = partial correctness + termination. Termination is expressed using 
  the weakest precondition calculus, i.e. @{term "pre S"} is the weakest precondition under
  which @{term S} terminates. \<close>

definition thoare_triple :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"thoare_triple P S Q = (hoare_triple P S Q \<and> `P \<longrightarrow> pre S`)"

syntax
  "_thoare" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(2H[_] /_) /[_]")

translations
  "_thoare P S Q" == "CONST thoare_triple (P)\<^sub>e S (Q)\<^sub>e"

lemma thoare_then_hoare: "H[P] C [Q] \<Longrightarrow> H{P} C {Q}"
  by (simp add: thoare_triple_def)

lemma thoareI: "\<lbrakk> H{P} C {Q}; `P \<longrightarrow> pre C` \<rbrakk> \<Longrightarrow> H[P] C [Q]"
  by (simp add: thoare_triple_def)

lemma thl_conseq:
  assumes "H[P\<^sub>2] S [Q\<^sub>2]" "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`Q\<^sub>2 \<longrightarrow> Q\<^sub>1`"
  shows "H[P\<^sub>1] S [Q\<^sub>1]"
  using assms 
  by (simp add: thoare_triple_def hoare_alt_def)
     (expr_auto, blast)

lemma thl_skip: "H[P] Skip [P]"
  by (auto simp add: thoare_triple_def hoare_alt_def terminates_Ret Skip_def)
     (metis (no_types, lifting) SEXP_def Skip_def tautI wp_Skip)

lemma thl_skip': 
  assumes "`P \<longrightarrow> Q`"
  shows "H[P] Skip [Q]"
  by (meson assms hl_skip' thl_skip thoare_triple_def)

lemma thl_seq: "\<lbrakk> H[P] S\<^sub>1 [Q]; H[Q] S\<^sub>2 [R] \<rbrakk> \<Longrightarrow> H[P] S\<^sub>1 ;; S\<^sub>2 [R]"
  by (auto simp add: thoare_triple_def hl_seq wp)
     (simp add: hoare_alt_def wp_alt_def seq_itree_def kleisli_comp_def, expr_auto, meson)

lemma thl_seq_inv [hoare_safe]: "\<lbrakk> H[P] S\<^sub>1 [P]; H[P] S\<^sub>2 [P] \<rbrakk> \<Longrightarrow> H[P] S\<^sub>1 ;; S\<^sub>2 [P]"
  by (simp add: thl_seq)

lemma thl_assigns: "H[\<sigma> \<dagger> P] \<langle>\<sigma>\<rangle>\<^sub>a [P]"
  by (simp add: thoare_triple_def hoare_assigns wp, subst_eval)

lemma thl_assign: "H[P\<lbrakk>e/x\<rbrakk>] x := e [P]"
  by (rule thl_assigns)

lemma thl_assigns_impl [hoare_safe]:
  assumes "`P \<longrightarrow> \<sigma> \<dagger> Q`"
  shows "H[P] \<langle>\<sigma>\<rangle>\<^sub>a [Q]"
  using assms by (auto intro: thl_conseq thl_assigns)

lemma thl_assign':
  assumes "`P \<longrightarrow> Q\<lbrakk>e/x\<rbrakk>`"
  shows "H[P] x := e [Q]"
  using assms by (fact thl_assigns_impl)

lemma thl_fwd_assign [hoare_safe]:
  assumes "vwb_lens x" "\<And> x\<^sub>0. H[$x = e\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> P\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>] S [Q]"
  shows "H[P] x := e ;; S [Q]"
  using assms
  by (auto simp add: thoare_triple_def hl_fwd_assign wp)
     (simp add: hoare_alt_def wp_alt_def, expr_auto
     ,metis assms(1) vwb_lens.put_eq vwb_lens_wb wb_lens_weak weak_lens_def)

lemma thl_assigns_bwd [hoare_safe]:
  assumes "H[P] S [\<sigma> \<dagger> Q]"
  shows "H[P] S ;; \<langle>\<sigma>\<rangle>\<^sub>a [Q]"
  by (blast intro: thl_seq[OF assms(1)] thl_assigns)

lemma thl_cond [hoare_safe]:
  assumes "H[B \<and> P] S [Q]" "H[\<not>B \<and> P] T [Q]"
  shows "H[P] if B then S else T fi [Q]"
  using assms by (simp add: thoare_triple_def hl_cond wp taut_def)

lemma thl_let [hoare_safe]:
  assumes "\<And> s. H[P \<and> \<guillemotleft>s\<guillemotright> = \<^bold>v] (S (e s)) [Q]"
  shows "H[P] let x \<leftarrow> e in S x [Q]"
  using assms
  by (auto intro: hl_let simp add: thoare_triple_def wp, expr_simp)

text \<open> For loops do not require a variant, as termination is guaranteed by construction \<close>

lemma thl_for:
  assumes "\<And> i. i < length xs \<Longrightarrow> H[@(R i)] S (xs ! i) [@(R (i+1))]"
  shows "H[@(R 0)] for i in \<guillemotleft>xs\<guillemotright> do S i od [@(R (length xs))]"
  using assms 
  by (simp add: thoare_triple_def hl_for pre_terminates)
     (force intro!: terminates_for_itree[of _ "R"] simp add: hoare_alt_def taut_def)

lemma thl_for_prestate:
  \<comment> \<open> The notation @{term "P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<rbrakk>"} means the @{term P} holds on the initial state @{term s\<^sub>0}. \<close>
  assumes 
    "\<And> s\<^sub>0 i. i < length (xs s\<^sub>0) \<Longrightarrow> H[@(R s\<^sub>0 i)] S (xs s\<^sub>0 ! i) [@(R s\<^sub>0 (i+1))]"
    "\<And> s\<^sub>0. `P \<and> \<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<longrightarrow> @(R s\<^sub>0 0)`"
    "\<And> s\<^sub>0. `@(R s\<^sub>0 (length (xs s\<^sub>0))) \<longrightarrow> Q`"
  shows "H[P] for i in xs do S i od [Q]"
  using assms
  apply (auto simp add: thoare_triple_def hl_for pre_terminates intro: hl_for_prestate)
   apply (rule hl_for_prestate[where R=R], auto)
  apply (expr_auto)
  apply (rule_tac terminates_for_itree_prestate[where R="R"], auto)
  apply (meson hoare_rel_triple_def)
  done

lemma thl_for_inv:
  assumes "\<And> i. i < length xs \<Longrightarrow> H[@(R i)] S (xs ! i) [@(R (i+1))]"
    "`P \<longrightarrow> @(R 0)`" "`@(R (length xs)) \<longrightarrow> Q`"
  shows "H[P] for x in \<guillemotleft>xs\<guillemotright> inv i. @(R i) do S x od [Q]"
  unfolding for_inv_def
  by (rule thl_conseq[OF thl_for[of xs R S, OF assms(1)]], simp_all add: assms)

lemma thl_for_inv_prestate [hoare_safe]:
  assumes 
    "\<And> s\<^sub>0 i. i < length (xs s\<^sub>0) \<Longrightarrow> H[@(R s\<^sub>0 i)] S (xs s\<^sub>0 ! i) [@(R s\<^sub>0 (i+1))]"
    "\<And> s\<^sub>0. `P \<and> \<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<longrightarrow> @(R s\<^sub>0 0)`"
    "\<And> s\<^sub>0. `@(R s\<^sub>0 (length (xs s\<^sub>0))) \<longrightarrow> Q`"
  shows "H[P] for i in xs inv i. @(R old i) do S i od [Q]"
  unfolding for_inv_def   
  using assms
  by (rule thl_for_prestate[where R=R], simp)

lemma for_to_inv_as_for_inv:
  "for i = m to n inv @(R old i) do S i od = for i in [m..<n + 1] inv i. @(R old i) do S i od"
  by (simp add: SEXP_def for_inv_def for_to_inv_code)

lemma thl_for_to_inv [hoare_safe]:
  assumes 
    "\<And> s\<^sub>0 i. \<lbrakk> m s\<^sub>0 \<le> i; i \<le> n s\<^sub>0 \<rbrakk> \<Longrightarrow> H[@(R s\<^sub>0 i)] S i [@(R s\<^sub>0 (i + 1))]"
    "\<And> s\<^sub>0. `P \<longrightarrow> @(R s\<^sub>0 (m s\<^sub>0))`" "\<And> s\<^sub>0. `@(R s\<^sub>0 (n s\<^sub>0+1 - m s\<^sub>0 + m s\<^sub>0)) \<longrightarrow> Q`"
  shows "H[P] for i = m to n inv @(R old i) do S i od [Q]"
proof -
  have 1:"\<And>s\<^sub>0 i. i < length [m s\<^sub>0..<n s\<^sub>0 + 1] \<Longrightarrow> H[@(R s\<^sub>0 (i + m s\<^sub>0))] S ([m s\<^sub>0..<n s\<^sub>0 + 1] ! i) [@(R s\<^sub>0 (i + 1 + m s\<^sub>0))]"
    by (smt (verit) Suc_eq_plus1 add.commute add_Suc_right assms(1) le_add2 length_upt less_Suc_eq_le less_diff_conv nth_upt)
  from assms(2) have 2:"\<And>s\<^sub>0. `P \<and> \<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<longrightarrow> @(R s\<^sub>0 (0 + m s\<^sub>0))`"
    by expr_auto
  from assms(3) have 3:"\<And>s\<^sub>0. `@(R s\<^sub>0 (length [m s\<^sub>0..<n s\<^sub>0 + 1] + m s\<^sub>0)) \<longrightarrow> Q`"
    by expr_simp (metis diff_is_0_eq' le_Suc_eq le_add_diff_inverse2 not_less_eq_eq)
  have "H[P] for_inv ([m..<n + 1])\<^sub>e (\<lambda>old i. (@(R old (i + m old)))\<^sub>e) S [Q]"
    by (rule thl_for_inv_prestate, fact 1, fact 2, fact 3)
  thus ?thesis
    by (metis SEXP_def for_inv_def for_to_inv_code)
qed

lemma thl_for_downto_inv [hoare_safe]:
  assumes 
    "\<And> s\<^sub>0 i. \<lbrakk> m s\<^sub>0 \<le> i; i \<le> n s\<^sub>0 \<rbrakk> \<Longrightarrow> H[@(R s\<^sub>0 i)] S i [@(R s\<^sub>0 (i - 1))]"
    "\<And> s\<^sub>0. `P \<longrightarrow> @(R s\<^sub>0 (n s\<^sub>0))`" "\<And> s\<^sub>0. `@(R s\<^sub>0 (n s\<^sub>0 - (Suc (n s\<^sub>0) - (m s\<^sub>0)))) \<longrightarrow> Q`"
  shows "H[P] for i = n downto m inv @(R old i) do S i od [Q]"
proof -
  have 1:"\<And>s\<^sub>0 i. i < length (rev [m s\<^sub>0..<n s\<^sub>0 + 1]) \<Longrightarrow> H[@(R s\<^sub>0 (n s\<^sub>0 - i))] S (rev [m s\<^sub>0..<n s\<^sub>0 + 1] ! i) [@(R s\<^sub>0 (n s\<^sub>0 - (i + 1)))]"
    apply (auto simp add: rev_nth nth_append)
    apply (smt (verit) Nat.add_diff_assoc2 add.commute assms(1) diff_diff_left diff_le_self le_add2 le_add_diff_inverse2 less_Suc_eq_le plus_1_eq_Suc)
    apply (smt (verit) One_nat_def assms(1) cancel_ab_semigroup_add_class.add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel cancel_comm_monoid_add_class.diff_zero diff_diff_left diff_le_self less_diff_conv linordered_semidom_class.add_diff_inverse nat_less_le not_less_eq)
    done
  from assms(2) have 2:"\<And>s\<^sub>0. `P \<and> \<guillemotleft>s\<^sub>0\<guillemotright> = $\<^bold>v \<longrightarrow> @(R s\<^sub>0 (n s\<^sub>0 - 0))`"
    by expr_auto
  from assms(3) have 3:"\<And>s\<^sub>0. `@(R s\<^sub>0 (n s\<^sub>0 - length (rev [m s\<^sub>0..<n s\<^sub>0 + 1]))) \<longrightarrow> Q`"
    apply expr_auto
    apply (metis One_nat_def Suc_diff_le Suc_eq_plus1 diff_diff_cancel diff_diff_eq)
    apply (metis diff_Suc_1' diff_Suc_Suc diff_is_0_eq' not_less_eq_eq)
    done

  have "H[P] for_inv (rev [m..<n + 1])\<^sub>e (\<lambda>old i. (@(R old (n old - i)))\<^sub>e) S [Q]"
    by (rule thl_for_inv_prestate, fact 1, fact 2, fact 3)
  thus ?thesis
    by (metis SEXP_def for_downto_inv_code for_inv_def)
qed

lemma thl_while [hoare_safe]:
  fixes V :: "'s \<Rightarrow> 'a::wellorder"
  assumes "\<And> z. H[P \<and> B \<and> V = \<guillemotleft>z\<guillemotright>] S [P \<and> V < \<guillemotleft>z\<guillemotright>]"
  shows "H[P] while B do S od [\<not> B \<and> P]"
proof -
  from assms have "\<^bold>{P \<and> B\<^bold>} S \<^bold>{P\<^bold>}"
    by (auto simp add: hoare_alt_def thoare_triple_def)
  hence partial: "\<^bold>{P\<^bold>} while B do S od \<^bold>{\<not> B \<and> P\<^bold>}"
    by (rule hoare_while_partial)
  from assms have S_term: "\<And> s. \<lbrakk> B s; P s \<rbrakk> \<Longrightarrow> terminates (S s)"
    by (simp add: thoare_triple_def pre_terminates, simp add: hoare_alt_def taut_def)  
  from assms have wS_term: "`P \<longrightarrow> pre (while B do S od)`"
    by (auto simp add: pre_terminates taut_def thoare_triple_def hoare_alt_def) 
       (auto intro!: terminates_iterate_wellorder_variant[of B P S V] simp add: SEXP_def)
  show ?thesis
    using partial thoareI wS_term by fastforce
qed

definition while_inv_var :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 'a::wellorder) \<Rightarrow> ('e, 's) htree \<Rightarrow> ('e, 's) htree" where
[code_unfold]: "while_inv_var B I V P = iterate B P"

syntax 
  "_while_inv_var_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(2while _ /inv/ _ /var/ _ /do/ _ /od)")
  "_while_inv_var_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(while _ /(2invariant/ _) /variant _ //(2do //_) //od)")
translations 
  "_while_inv_var_itree B I V P" => "CONST while_inv_var (B)\<^sub>e (\<lambda> _ghost_old. (I)\<^sub>e) (V)\<^sub>e P"
  "_while_inv_var_itree B I V P" <= "CONST while_inv_var (B)\<^sub>e (\<lambda> g. (I)\<^sub>e) (V)\<^sub>e P"

lemma thl_prestate:
  assumes "\<And> old. H[\<guillemotleft>old\<guillemotright> = $\<^bold>v \<and> P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk>] C [Q]"
  shows "H[P] C [Q]"
  using assms 
  using assms by (simp add: thoare_triple_def hoare_alt_def lens_defs, expr_auto)

lemma thl_frame_rule:
  assumes "C nmods I" "H[P] C [Q]"
  shows "H[I \<and> P] C [I \<and> Q]"
  using assms by (force simp add: thoare_triple_def hoare_alt_def not_modifies_def taut_def retvals_def)

lemma thl_frame_rule':
  assumes "C nmods I" "H[I \<and> P] C [Q]"
  shows "H[I \<and> P] C [I \<and> Q]"
  using assms by (force simp add: thoare_triple_def hoare_alt_def not_modifies_def taut_def retvals_def)

lemma hl_frame_rule':
  assumes "C nmods I" "H{I \<and> P} C {Q}"
  shows "H{I \<and> P} C {I \<and> Q}"
  using assms by (force simp add: hoare_alt_def not_modifies_def retvals_def)

lemma thl_while_inv_prestate [hoare_safe]:
  assumes 
    \<comment> \<open> The notation @{term "P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk>"} means the @{term P} holds on the initial state @{term old}. \<close>
    "\<And> old z. H[P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I old) \<and> B \<and> V = \<guillemotleft>z\<guillemotright>] S [@(I old) \<and> V < \<guillemotleft>z\<guillemotright>]" 
    "\<And> old. `P \<and> \<guillemotleft>old\<guillemotright> = $\<^bold>v \<longrightarrow> @(I old)`" 
    "\<And> old. `(P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> \<not> B \<and> @(I old)) \<longrightarrow> Q`"
  shows "H[P]while B inv @(I old) var V do S od[Q]"
proof (rule_tac thl_prestate)
  fix old
  show "H[\<guillemotleft>old\<guillemotright> = $\<^bold>v \<and> P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk>] while B inv @(I old) var V do S od [Q]"
  proof -
    have "\<And> z. H[(P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I old)) \<and> B \<and> V = \<guillemotleft>z\<guillemotright>] S [(P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I old)) \<and> V < \<guillemotleft>z\<guillemotright>]"
    proof (simp, rule thl_frame_rule')
      fix z
      show "S nmods P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk>"
        by (expr_simp add: not_modifies_def)
      show "\<And> z. H[P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I old) \<and> B \<and> V = \<guillemotleft>z\<guillemotright>] S [@(I old) \<and> V < \<guillemotleft>z\<guillemotright>]"
        by (fact assms(1))
    qed
    hence w:"H[P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I old)] while B do S od [\<not> B \<and> P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(I old)]"
      by (rule thl_while)
    from assms(2-3) show ?thesis
      unfolding while_inv_var_def
      by (rule_tac thl_conseq[OF w]; expr_auto)
  qed
qed

lemma thl_while_inv_var [hoare_safe]:
  assumes "\<And> z. H[I \<and> B \<and> V = \<guillemotleft>z\<guillemotright>] S [I \<and> V < \<guillemotleft>z\<guillemotright>]" "`P \<longrightarrow> I`" "`(\<not> B \<and> I) \<longrightarrow> Q`"
  shows "H[P] while B inv I var V do S od [Q]"
  unfolding while_inv_var_def
  by (auto intro!: thl_conseq[OF _ assms(2) assms(3)] thl_while assms(1))

text \<open> The next law is a degenerate partial correctness law, which ignores the variant. \<close>

lemma hl_while_inv_var [hoare_safe]:
  assumes "\<^bold>{I \<and> B\<^bold>} S \<^bold>{I\<^bold>}" "`P \<longrightarrow> I`" "`(\<not> B \<and> I) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>}while B inv I var V do S od\<^bold>{Q\<^bold>}"
proof -
  have "while B inv I var V do S od = while B inv I do S od"
    by (simp add: while_inv_var_def while_inv_def)
  with assms show ?thesis
    apply simp
    apply (rule hl_while_inv)
    by (simp add: hl_while_inv)
qed

lemma thl_via_wlp_wp: "H[P] S [Q] = `P \<longrightarrow> (wlp S Q \<and> pre S)`"
  by (simp add: thoare_triple_def hl_via_wlp, expr_auto)

end