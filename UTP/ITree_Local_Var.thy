theory ITree_Local_Var
  imports ITree_Hoare
begin

zstore lvar =
  lstack :: "int list"

definition open_var :: "('e, 'a lvar_scheme) htree" where
"open_var = (lstack := lstack @ [0])"

definition close_var :: "('e, 'a lvar_scheme) htree" where
"close_var = (lstack := butlast lstack)"

definition "lvar_lens l = (list_lens (length l - 1) ;\<^sub>L lstack)"

lemma mwb_lvar_lens [simp]: "mwb_lens (lvar_lens s)"
  by (simp add: lvar_lens_def list_mwb_lens comp_mwb_lens)

definition vblock :: "((int \<Longrightarrow> 'a lvar_scheme) \<Rightarrow> ('e, 'a lvar_scheme) htree) \<Rightarrow> ('e, 'a lvar_scheme) htree"
  where "vblock B = open_var ;; let_itree (SEXP (\<lambda> s. (lvar_lens (get\<^bsub>lstack\<^esub> s)))) B ;; close_var"

syntax "_vblock" :: "id \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var _ :: _./ _" [0, 0, 10] 10)

translations 
  "_vblock x t e" => "CONST vblock (_lvar_abs x t e)"

definition "lv_at x n = (\<lambda> s. length (get\<^bsub>lstack\<^esub> s) > n 
                        \<and> x = list_lens (length (get\<^bsub>lstack\<^esub> s) - Suc n) ;\<^sub>L lstack)"

expr_constructor lv_at

lemma lv_at_indep_out_stack1 [simp]: "\<lbrakk> lv_at x n s; lstack \<bowtie> y \<rbrakk> \<Longrightarrow> x \<bowtie> y"
  by (simp add: lens_indep_left_ext lv_at_def) 

lemma lv_at_indep_out_stack2 [simp]: "\<lbrakk> lv_at x n s; lstack \<bowtie> y \<rbrakk> \<Longrightarrow> y \<bowtie> x"
  by (metis lens_indep_right_ext lens_indep_sym lv_at_def)

lemma lv_at_indep_in_stack [simp]: "\<lbrakk> lv_at x m s; lv_at y n s; m \<noteq> n \<rbrakk> \<Longrightarrow> x \<bowtie> y"
  by (simp add: lv_at_def lens_comp_indep_cong)
     (metis cancel_semigroup_add_class.add_left_imp_eq diff_diff_cancel less_eq_Suc_le list_lens_indep plus_1_eq_Suc)

lemma lv_at_grow_stack_1 [usubst]: "(lv_at x n)\<lbrakk>butlast lstack/lstack\<rbrakk> = lv_at x (n + 1)"
  by (auto simp add: lv_at_def subst_app_def subst_upd_def fun_eq_iff)

lemma lv_at_grow_stack_2 [simp]: "lv_at x n ([lstack \<leadsto> butlast ($lstack)] s) = lv_at x (n + 1) s"
  by (auto simp add: lv_at_def subst_app_def subst_upd_def fun_eq_iff)

lemma hl_vblock [hoare_safe]:
  assumes "\<And> x. mwb_lens x 
                  \<Longrightarrow> H{lv_at x 0 \<and> P\<lbrakk>butlast lstack/lstack\<rbrakk>} B x {Q\<lbrakk>butlast lstack/lstack\<rbrakk>}"
  shows "H{P} vblock (\<lambda> x. B x) {Q}"
  apply (simp add: vblock_def open_var_def close_var_def)
  apply (rule hoare_safe)
   apply simp
  apply (rule hoare_safe)
  apply (rule hoare_safe)
  apply (rule hl_conseq)
    apply (rule assms(1))
    apply (simp add: lv_at_def)
   apply (simp add: lv_at_def lvar_lens_def)
   apply expr_simp
  apply expr_simp
  done

zstore swap = lvar +
  x :: int
  y :: int

lit_vars

definition prog :: "(unit, swap) htree" where 
"prog = (var temp2::int. var temp::int. temp := x ;; x := y ;; y := temp)"

lemma "H{x = X \<and> y = Y} prog {x = Y \<and> y = X}"
  unfolding prog_def
  apply (rule hl_vblock)
  apply (rule hl_vblock)
  apply (subst_eval)
  apply vcg_lens
  done
  
def_consts MAX_SIL_STEPS = 100

execute "x := 1 ;; y := 2 ;; prog"

end