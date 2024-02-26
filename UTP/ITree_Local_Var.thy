section \<open> Local Variable Blocks \<close>

theory ITree_Local_Var
  imports ITree_Hoare
begin

subsection \<open> Injection Universe \<close>

text \<open> We introduce a simple injection universe to support local variable 
       stacks. For now, we only support non-inductive data structures, but
       inductive data structures could be supported by adding n-ary trees. \<close>

datatype utype =
  UnitT | BoolT | NatT | IntT | RatT | RealT | StringT | ListT utype | ProdT utype utype | SumT utype utype

datatype uval =
  UnitV | BoolV bool | NatV nat | IntV int | RatV rat | RealV real | StringV "String.literal" | 
  ListV utype "uval list" | ProdV "uval \<times> uval" | SumV utype utype "uval + uval"

fun uval_type :: "uval \<Rightarrow> utype option" where
"uval_type UnitV = Some UnitT" |
"uval_type (BoolV _) = Some BoolT" |
"uval_type (NatV _) = Some NatT" |
"uval_type (IntV _) = Some IntT" | 
"uval_type (RatV _) = Some RatT" |
"uval_type (RealV _) = Some RealT" |
"uval_type (StringV _) = Some StringT" |
"uval_type (ListV t xs) = (if (\<forall> x\<in>set xs. uval_type x = Some t) then Some (ListT t) else None)" |
"uval_type (ProdV (x, y)) = (case (uval_type x, uval_type y) of (Some a, Some b) \<Rightarrow> Some (ProdT a b) | _ \<Rightarrow> None)" |
"uval_type (SumV a b x) = (if (case x of Inl l \<Rightarrow> uval_type l = Some a | Inr r \<Rightarrow> uval_type r = Some b) then Some (SumT a b) else None)" 

text \<open> Any type we wish to use in local variables need to instantiate the 
       following class. \<close>

class injval =
  fixes inj_val :: "'a \<Rightarrow> uval"
  and proj_val :: "uval \<Rightarrow> 'a option"
  and utyp :: "'a itself \<Rightarrow> utype"
  assumes inj_val_inv [simp]: "proj_val (inj_val x) = Some x"
  and val_type [simp]: "uval_type (inj_val x) = Some (utyp TYPE('a))" 

instantiation unit :: injval
begin
definition inj_val_unit :: "unit \<Rightarrow> uval" where "inj_val_unit _ = UnitV"
fun proj_val_unit :: "uval \<Rightarrow> unit option" where "proj_val x = (case x of UnitV \<Rightarrow> Some () | _ \<Rightarrow> None)"
definition utyp_unit :: "unit itself \<Rightarrow> utype" where "utyp_unit t = UnitT"
instance by (intro_classes, auto simp add: inj_val_unit_def utyp_unit_def)
end

instantiation bool :: injval
begin
definition inj_val_bool :: "bool \<Rightarrow> uval" where "inj_val_bool = BoolV"
fun proj_val_bool :: "uval \<Rightarrow> bool option" where "proj_val x = (case x of BoolV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_bool :: "bool itself \<Rightarrow> utype" where "utyp_bool t = BoolT"
instance by (intro_classes, auto simp add: inj_val_bool_def utyp_bool_def)
end

instantiation nat :: injval
begin
definition inj_val_nat :: "nat \<Rightarrow> uval" where "inj_val_nat = NatV"
fun proj_val_nat :: "uval \<Rightarrow> nat option" where "proj_val x = (case x of NatV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_nat :: "nat itself \<Rightarrow> utype" where "utyp_nat t = NatT"
instance by (intro_classes, auto simp add: inj_val_nat_def utyp_nat_def)
end

instantiation int :: injval
begin
definition inj_val_int :: "int \<Rightarrow> uval" where "inj_val_int = IntV"
fun proj_val_int :: "uval \<Rightarrow> int option" where "proj_val x = (case x of IntV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_int :: "int itself \<Rightarrow> utype" where "utyp_int t = IntT"
instance by (intro_classes, auto simp add: inj_val_int_def utyp_int_def)
end

instantiation rat :: injval
begin
definition inj_val_rat :: "rat \<Rightarrow> uval" where "inj_val_rat = RatV"
fun proj_val_rat :: "uval \<Rightarrow> rat option" where "proj_val x = (case x of RatV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_rat :: "rat itself \<Rightarrow> utype" where "utyp_rat t = RatT"
instance by (intro_classes, auto simp add: inj_val_rat_def utyp_rat_def)
end

instantiation real :: injval
begin
definition inj_val_real :: "real \<Rightarrow> uval" where "inj_val_real = RealV"
fun proj_val_real :: "uval \<Rightarrow> real option" where "proj_val x = (case x of RealV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_real :: "real itself \<Rightarrow> utype" where "utyp_real t = RealT"
instance by (intro_classes, auto simp add: inj_val_real_def utyp_real_def)
end

instantiation String.literal :: injval
begin
definition inj_val_literal :: "String.literal \<Rightarrow> uval" where "inj_val_literal = StringV"
fun proj_val_literal :: "uval \<Rightarrow> String.literal option" where "proj_val x = (case x of StringV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_literal :: "String.literal itself \<Rightarrow> utype" where "utyp_literal t = StringT"
instance by (intro_classes, auto simp add: inj_val_literal_def utyp_literal_def)
end

instantiation list :: (injval) injval
begin
definition inj_val_list :: "'a list \<Rightarrow> uval" where "inj_val_list xs = ListV (utyp TYPE('a)) (map inj_val xs)"
definition proj_val_list :: "uval \<Rightarrow> 'a list option" 
  where "proj_val x = (case x of ListV a xs \<Rightarrow> let ys = map proj_val xs in (if None \<in> set ys then None else Some (map the ys)) |
                                 _ \<Rightarrow> None)"
definition utyp_list :: "'a list itself \<Rightarrow> utype" where "utyp_list t = ListT (utyp TYPE('a))"
instance by (intro_classes, auto simp add: inj_val_list_def proj_val_list_def utyp_list_def list.map_ident_strong)
end

instantiation prod :: (injval, injval) injval
begin
definition inj_val_prod :: "'a \<times> 'b \<Rightarrow> uval" where
"inj_val_prod = (\<lambda> (x, y). ProdV (inj_val x, inj_val y))"

definition proj_val_prod :: "uval \<Rightarrow> ('a \<times> 'b) option" where
"proj_val_prod v = (case v of ProdV (x, y) \<Rightarrow> 
                      (case (proj_val x, proj_val y) of (Some x', Some y') \<Rightarrow> Some (x', y') | _ \<Rightarrow> None) |  
                      _ \<Rightarrow> None)"

definition utyp_prod :: "('a \<times> 'b) itself \<Rightarrow> utype" where "utyp_prod _ = ProdT (utyp TYPE('a)) (utyp TYPE('b))"

instance by (intro_classes, auto simp add: inj_val_prod_def proj_val_prod_def utyp_prod_def)

end

instantiation sum :: (injval, injval) injval
begin
definition inj_val_sum :: "'a + 'b \<Rightarrow> uval" where
"inj_val_sum = (\<lambda> x. SumV (utyp TYPE('a)) (utyp TYPE('b)) (map_sum inj_val inj_val x))"

definition proj_val_sum :: "uval \<Rightarrow> ('a + 'b) option" where
"proj_val_sum v = (case v of 
                   SumV _ _ (Inl x) \<Rightarrow> map_option Inl (proj_val x) |
                   SumV _ _ (Inr x) \<Rightarrow> map_option Inr (proj_val x) |
                   _ \<Rightarrow> None)"

definition utyp_sum :: "('a + 'b) itself \<Rightarrow> utype" where "utyp_sum _ = SumT (utyp TYPE('a)) (utyp TYPE('b))"

instance by (intro_classes, auto simp add: sum.case_eq_if inj_val_sum_def proj_val_sum_def utyp_sum_def isl_map_sum map_sum_sel)

end

subsection \<open> Value projection lens \<close>

definition uval_lens :: "'a::injval \<Longrightarrow> uval" where
"uval_lens = \<lparr> lens_get = (\<lambda> s. the (proj_val s)), lens_put = (\<lambda> s v. inj_val v) \<rparr>"  

lemma mwb_uval_lens [simp]: "mwb_lens uval_lens"
  by (unfold_locales, simp_all add: uval_lens_def)

subsection \<open> Local Variable Stack \<close>

zstore lvar =
  lstack :: "uval list"

text \<open> Extend the variable stack \<close>

definition open_var :: "('e, 'a lvar_scheme) htree" where
"open_var = (lstack := lstack @ [UnitV])"

text \<open> Reduce the variable stack \<close>

definition close_var :: "('e, 'a lvar_scheme) htree" where
"close_var = (lstack := butlast lstack)"

text \<open> A lens pointing to one of the locations in the stack \<close>

definition lvar_lens :: "'s lvar_scheme \<Rightarrow> ('v::injval \<Longrightarrow> 's lvar_scheme)" where 
"lvar_lens s = (uval_lens ;\<^sub>L list_lens (length (get\<^bsub>lstack\<^esub> s) - 1) ;\<^sub>L lstack)"

lemma mwb_lvar_lens [simp]: "mwb_lens (lvar_lens s)"
  by (simp add: lvar_lens_def list_mwb_lens comp_mwb_lens)

text \<open> The next predicate characterises the location of a local variable in the stack. \<close>

definition lv_at :: "('v::injval \<Longrightarrow> 's lvar_scheme) \<Rightarrow> nat \<Rightarrow> 's lvar_scheme \<Rightarrow> bool" where 
  "lv_at x n = (\<lambda> s. length (get\<^bsub>lstack\<^esub> s) > n 
               \<and> x = uval_lens ;\<^sub>L list_lens (length (get\<^bsub>lstack\<^esub> s) - Suc n) ;\<^sub>L lstack)"

expr_constructor lv_at

lemma lv_at_indep_out_stack1 [simp]: "\<lbrakk> lv_at x n s; lstack \<bowtie> y \<rbrakk> \<Longrightarrow> x \<bowtie> y"
  by (simp add: lens_indep_left_ext lv_at_def) 

lemma lv_at_indep_out_stack2 [simp]: "\<lbrakk> lv_at x n s; lstack \<bowtie> y \<rbrakk> \<Longrightarrow> y \<bowtie> x"
  by (metis lens_indep_right_ext lens_indep_sym lv_at_def)

lemma lv_at_indep_in_stack [simp]: "\<lbrakk> lv_at x m s; lv_at y n s; m \<noteq> n \<rbrakk> \<Longrightarrow> x \<bowtie> y"
  by (simp add: lv_at_def lens_comp_indep_cong)
     (metis Suc_diff_Suc diff_less_mono2 lens_indep_left_ext lens_indep_right_ext list_lens_indep nat_neq_iff)
     
lemma lv_at_grow_stack_1 [usubst]: "(lv_at x n)\<lbrakk>butlast lstack/lstack\<rbrakk> = lv_at x (n + 1)"
  by (auto simp add: lv_at_def subst_app_def subst_upd_def fun_eq_iff)

lemma lv_at_grow_stack_2 [simp]: "lv_at x n ([lstack \<leadsto> butlast ($lstack)] s) = lv_at x (n + 1) s"
  by (auto simp add: lv_at_def subst_app_def subst_upd_def fun_eq_iff)

subsection \<open> Variable Blocks \<close>

definition vblock :: "'v itself \<Rightarrow> (('v::injval \<Longrightarrow> 'a lvar_scheme) \<Rightarrow> ('e, 'a lvar_scheme) htree) \<Rightarrow> ('e, 'a lvar_scheme) htree"
  where "vblock t B = open_var ;; let_itree (SEXP lvar_lens) B ;; close_var"

syntax "_vblock" :: "id \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var _ :: _./ _" [0, 0, 10] 10)

translations 
  "_vblock x t e" => "CONST vblock (_TYPE t) (_lvar_abs x t e)"
  "_vblock x t e" <= "CONST vblock (_TYPE t) (\<lambda> x. e)"

lemma hl_vblock [hoare_safe]:
  assumes "\<And> x. mwb_lens x 
                  \<Longrightarrow> H{lv_at x 0 \<and> P\<lbrakk>butlast lstack/lstack\<rbrakk>} B x {Q\<lbrakk>butlast lstack/lstack\<rbrakk>}"
  shows "H{P} var x :: 't::injval. B x {Q}"
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

end