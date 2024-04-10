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

definition uvals :: "utype \<Rightarrow> uval set" where
"uvals t = {v. uval_type v = Some t}" 

lemma uvals: 
  "uvals UnitT = {UnitV}" "uvals BoolT = range BoolV" "uvals NatT = range NatV"
  "uvals IntT = range IntV" "uvals RatT = range RatV" "uvals RealT = range RealV"
  "uvals StringT = range StringV" "uvals (ListT a) = {ListV a xs | xs. set xs \<subseteq> uvals a}"
  "uvals (ProdT a b) = {ProdV (x, y) | x y. x \<in> uvals a \<and> y \<in> uvals b}"
  by (auto simp add: uvals_def, (case_tac x, auto simp add: option.case_eq_if)+)

lemma uvals_SumT: "uvals (SumT a b) = {SumV a b (Inl x) | x. x \<in> uvals a} \<union> {SumV a b (Inr y) | y. y \<in> uvals b}"
  by (auto simp add: uvals_def, case_tac x, auto simp add: option.case_eq_if sum.case_eq_if)
     (metis sum.collapse(1) sum.collapse(2))

fun uval_default :: "utype \<Rightarrow> uval" where
"uval_default UnitT = UnitV" |
"uval_default BoolT = BoolV True" |
"uval_default NatT = NatV 0" |
"uval_default IntT = IntV 0" |
"uval_default RatT = RatV 0" |
"uval_default RealT = RealV 0" |
"uval_default StringT = StringV STR ''''" |
"uval_default (ListT a) = ListV a []" |
"uval_default (ProdT a b) = ProdV (uval_default a, uval_default b)" |
"uval_default (SumT a b) = SumV a b (Inl (uval_default a))"

lemma uval_default_type [simp]: "uval_type (uval_default a) = Some a"
  by (induct a; simp)

text \<open> Any type we wish to use in local variables need to instantiate the 
       following class. \<close>

class injval =
  fixes inj_val :: "'a \<Rightarrow> uval"
  and proj_val :: "uval \<Rightarrow> 'a option"
  and utyp :: "'a itself \<Rightarrow> utype"
  assumes inj_val_inv [simp]: "proj_val (inj_val x) = Some x"
  and val_type [simp]: "uval_type (inj_val x) = Some (utyp TYPE('a))"
  and proj_val_inv: "y \<in> uvals (utyp TYPE('a)) \<Longrightarrow> inj_val (the (proj_val y)) = y"
begin

lemma inj_val: "inj inj_val"
  by (metis injI local.inj_val_inv option.sel)

lemma ran_proj_val: "ran proj_val = UNIV"
  by (metis UNIV_eq_I local.inj_val_inv ranI)

lemma proj_val_nNone: "uval_type x = Some (utyp TYPE('a)) \<Longrightarrow> proj_val x \<noteq> None"
  using local.proj_val_inv option.discI uvals_def by fastforce

lemma inj_val_typed [simp]: "inj_val x \<in> uvals (utyp TYPE('a))"
  by (simp add: uvals_def)

end

instantiation unit :: injval
begin
definition inj_val_unit :: "unit \<Rightarrow> uval" where "inj_val_unit _ = UnitV"
fun proj_val_unit :: "uval \<Rightarrow> unit option" where "proj_val x = (case x of UnitV \<Rightarrow> Some () | _ \<Rightarrow> None)"
definition utyp_unit :: "unit itself \<Rightarrow> utype" where "utyp_unit t = UnitT"
instance by (intro_classes, auto simp add: inj_val_unit_def utyp_unit_def uvals)
end

instantiation bool :: injval
begin
definition inj_val_bool :: "bool \<Rightarrow> uval" where "inj_val_bool = BoolV"
fun proj_val_bool :: "uval \<Rightarrow> bool option" where "proj_val x = (case x of BoolV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_bool :: "bool itself \<Rightarrow> utype" where "utyp_bool t = BoolT"
instance by (intro_classes, auto simp add: inj_val_bool_def utyp_bool_def uvals)
end

instantiation nat :: injval
begin
definition inj_val_nat :: "nat \<Rightarrow> uval" where "inj_val_nat = NatV"
fun proj_val_nat :: "uval \<Rightarrow> nat option" where "proj_val x = (case x of NatV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_nat :: "nat itself \<Rightarrow> utype" where "utyp_nat t = NatT"
instance by (intro_classes, auto simp add: inj_val_nat_def utyp_nat_def uvals)
end

instantiation int :: injval
begin
definition inj_val_int :: "int \<Rightarrow> uval" where "inj_val_int = IntV"
fun proj_val_int :: "uval \<Rightarrow> int option" where "proj_val x = (case x of IntV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_int :: "int itself \<Rightarrow> utype" where "utyp_int t = IntT"
instance by (intro_classes, auto simp add: inj_val_int_def utyp_int_def uvals)
end

instantiation rat :: injval
begin
definition inj_val_rat :: "rat \<Rightarrow> uval" where "inj_val_rat = RatV"
fun proj_val_rat :: "uval \<Rightarrow> rat option" where "proj_val x = (case x of RatV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_rat :: "rat itself \<Rightarrow> utype" where "utyp_rat t = RatT"
instance by (intro_classes, auto simp add: inj_val_rat_def utyp_rat_def uvals)
end

instantiation real :: injval
begin
definition inj_val_real :: "real \<Rightarrow> uval" where "inj_val_real = RealV"
fun proj_val_real :: "uval \<Rightarrow> real option" where "proj_val x = (case x of RealV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_real :: "real itself \<Rightarrow> utype" where "utyp_real t = RealT"
instance by (intro_classes, auto simp add: inj_val_real_def utyp_real_def uvals)
end

instantiation String.literal :: injval
begin
definition inj_val_literal :: "String.literal \<Rightarrow> uval" where "inj_val_literal = StringV"
fun proj_val_literal :: "uval \<Rightarrow> String.literal option" where "proj_val x = (case x of StringV n \<Rightarrow> Some n | _ \<Rightarrow> None)"
definition utyp_literal :: "String.literal itself \<Rightarrow> utype" where "utyp_literal t = StringT"
instance by (intro_classes, auto simp add: inj_val_literal_def utyp_literal_def uvals)
end

instantiation list :: (injval) injval
begin
definition inj_val_list :: "'a list \<Rightarrow> uval" where "inj_val_list xs = ListV (utyp TYPE('a)) (map inj_val xs)"
definition proj_val_list :: "uval \<Rightarrow> 'a list option" 
  where "proj_val x = (case x of ListV a xs \<Rightarrow> let ys = map proj_val xs in (if None \<in> set ys then None else Some (map the ys)) |
                                 _ \<Rightarrow> None)"
definition utyp_list :: "'a list itself \<Rightarrow> utype" where "utyp_list t = ListT (utyp TYPE('a))"
instance 
  by (intro_classes, auto simp add: inj_val_list_def proj_val_list_def utyp_list_def uvals list.map_ident_strong proj_val_inv subsetD)
     (metis inj_val_inv option.distinct(1) proj_val_inv subsetD)
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

instance 
  by (intro_classes, auto simp add: inj_val_prod_def proj_val_prod_def utyp_prod_def uvals)
     (metis (no_types, lifting) case_prod_conv inj_val_inv option.sel option.simps(5) proj_val_inv)
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

instance 
  by (intro_classes, auto simp add: sum.case_eq_if inj_val_sum_def proj_val_sum_def utyp_sum_def isl_map_sum map_sum_sel uvals_SumT)
     (metis inj_val_inv map_sum.simps option.distinct(1) option.map_sel proj_val_inv)+
end

subsection \<open> Value projection lens \<close>

definition uval_lens :: "'a::injval \<Longrightarrow> uval" where
"uval_lens = \<lparr> lens_get = (\<lambda> s. the (proj_val s)), lens_put = (\<lambda> s v. inj_val v) \<rparr>"  

lemma mwb_uval_lens [simp]: "mwb_lens uval_lens"
  by (unfold_locales, simp_all add: uval_lens_def)

lemma source_uval_lens: "\<S>\<^bsub>uval_lens :: 'a::injval \<Longrightarrow> uval\<^esub> = uvals (utyp TYPE('a))"
  by (auto simp add: lens_source_def uval_lens_def, metis proj_val_inv) 

instantiation uval :: default
begin
definition default_uval :: "uval" where
"default_uval = UnitV"
instance ..
end

instance uval :: two
proof
  have "infinite (UNIV :: uval set)"
  proof 
    assume "finite (UNIV :: uval set)"
    hence f: "finite (NatV ` UNIV)"
      by (meson finite_subset subset_UNIV)
    have inj: "inj NatV"
      by (metis inj_val inj_val_nat_def)
    have "finite (UNIV :: nat set)"
      using f finite_imageD inj by blast
    thus False
      by simp
  qed
  thus "infinite (UNIV :: uval set) \<or> 2 \<le> card UNIV"
    by auto
qed

subsection \<open> Local Variable Stack \<close>

type_synonym uname = "String.literal"

text \<open> We model the store as a partial function from names (strings) to values in the 
  universe defined above. \<close>

zstore lvar =
  lstore :: "uname \<Zpfun> uval"

subsection \<open> Identifiers as Strings \<close>

text \<open> Each local variable is assigned the same name as the Isabelle identifier used to introduce
  the name in the binder. For this reason, we need to convert identifiers into strings. \<close>

syntax
  "_id_string"     :: "id \<Rightarrow> string" ("IDSTR'(_')")
  "_id_literal"    :: "id \<Rightarrow> String.literal" ("IDLIT'(_')")

parse_translation \<open>
let
  fun id_string_tr [Free (full_name, _)] = HOLogic.mk_string full_name
    | id_string_tr [Const (full_name, _)] = HOLogic.mk_string full_name
    | id_string_tr _ = raise Match;
  fun id_literal_tr [Free (full_name, _)] = HOLogic.mk_literal full_name
    | id_literal_tr [Const (full_name, _)] = HOLogic.mk_literal full_name
    | id_literal_tr _ = raise Match;

in
  [(@{syntax_const "_id_string"}, K id_string_tr)
  ,(@{syntax_const "_id_literal"}, K id_literal_tr)]
end
\<close>

subsection \<open> Local Variable Lenses \<close>

text \<open> The local variable lens projects the store, followed by the value (@{typ uval}) at the given 
  name, followed by projecting out a value of the correct type. \<close>

definition lvar_lens :: "uname \<Rightarrow> ('a::injval \<Longrightarrow> 's lvar_scheme)" where 
"lvar_lens n = (uval_lens ;\<^sub>L pfun_lens n ;\<^sub>L lstore)" 

lemma mwb_lvar_lens [simp]: "mwb_lens (lvar_lens n)"
  by (simp add: comp_mwb_lens lvar_lens_def)

lemma pfun_lens_indep: "x \<noteq> y \<Longrightarrow> pfun_lens x \<bowtie> pfun_lens y"
  by (unfold_locales, simp_all add: pfun_lens_def pfun_upd_comm)

lemma lvar_lens_indep [simp]: "m \<noteq> n \<Longrightarrow> lvar_lens m \<bowtie> lvar_lens n"
  by (simp add: lvar_lens_def pfun_lens_indep lens_indep_left_ext lens_indep_right_ext)

lemma get_pfun_lens: "get\<^bsub>pfun_lens i\<^esub> s = s(i)\<^sub>p"
  by (simp add: pfun_lens_def)

lemma vwb_src_UNIV [simp]: "vwb_lens X \<Longrightarrow> \<S>\<^bsub>X\<^esub> = UNIV"
  by (meson vwb_lens_iff_mwb_UNIV_src)

text \<open> A local variable lens is defined when its name is in the domain of the store, and the value
  at that name has the correct type. \<close>

lemma source_lvar_lens: 
  "\<S>\<^bsub>lvar_lens n :: 'a::injval \<Longrightarrow> _\<^esub> 
   = {s. n \<in> pdom (get\<^bsub>lstore\<^esub> s) \<and> pfun_app (get\<^bsub>lstore\<^esub> s) n \<in> uvals (utyp TYPE('a::injval))}"
  by (simp add: lvar_lens_def lens_defined_def comp_mwb_lens source_lens_comp pfun_lens_src source_uval_lens univ_var_def id_lens_def get_pfun_lens)

definition lv_lens :: "('a::injval \<Longrightarrow> 's lvar_scheme) \<Rightarrow> uname \<Rightarrow> bool" where
"lv_lens x n = (x = lvar_lens n)"

syntax "_lv_lens" :: "id \<Rightarrow> logic" ("lvlens'(_')")
translations 
  "lvlens(x)" => "CONST lv_lens x IDLIT(x)"
  "lvlens(x)" <= "CONST lv_lens x y"

text \<open> For convenience, we allow the notation @{term "lvlens(x)"} to state that the lens bound
  to identifier @{term x} is a local variable lens with the name @{term "STR ''x''"}. \<close>

lemma mwb_lv_lens [simp]: "lv_lens x n \<Longrightarrow> mwb_lens x"
  by (simp add: lv_lens_def)

lemma lv_lens_indep_1 [simp]: "\<lbrakk> lv_lens x n; y \<bowtie> lstore \<rbrakk> \<Longrightarrow> x \<bowtie> y"
  by (metis lens_indep_right_ext lens_indep_sym lv_lens_def lvar_lens_def)

lemma lv_lens_indep_2 [simp]: "\<lbrakk> lv_lens x n; y \<bowtie> lstore \<rbrakk> \<Longrightarrow> y \<bowtie> x"
  by (meson lens_indep_sym lv_lens_indep_1)

lemma lv_lens_indep_3 [simp]: "\<lbrakk> lv_lens x m; lv_lens y n; m \<noteq> n \<rbrakk> \<Longrightarrow> x \<bowtie> y"
  by (metis lv_lens_def lvar_lens_indep)

text \<open> The next predicate characterises that a given lens is defined in a particular state. \<close>

definition lvname :: "('a::injval \<Longrightarrow> 's lvar_scheme) \<Rightarrow> uname \<Rightarrow> 'a itself \<Rightarrow> 's lvar_scheme \<Rightarrow> bool" where 
[expr_defs]: "lvname x n t = (\<guillemotleft>n\<guillemotright> \<in> pdom lstore \<and> lstore(\<guillemotleft>n\<guillemotright>)\<^sub>p \<in> uvals (utyp TYPE('a)))\<^sub>e"

expr_constructor lvname

lemma lv_lens_defined [simp]: "lv_lens x n \<Longrightarrow> \<^bold>D(x) = lvname x n TYPE('t::injval)"
  by (expr_simp add: lv_lens_def source_lvar_lens)

lemma lvname_subst_1 [simp]: "y \<bowtie> lstore \<Longrightarrow> lvname x n t ([y \<leadsto> e] s) = lvname x n t s"
  by (simp add: lens_indep.lens_put_irr2 lvname_def subst_id_def subst_upd_def)

lemma lvname_subst_2 [simp]: "\<lbrakk> lv_lens x m; lv_lens y n; m \<noteq> n \<rbrakk> \<Longrightarrow> lvname x m t ([y \<leadsto> e] s) = lvname x m t s"
  by (auto simp add: lvname_def subst_upd_def subst_id_def lens_comp_def lv_lens_def lvar_lens_def pfun_lens_def)

lemma lvname_subst_3 [simp]: "\<lbrakk> lv_lens x m; m \<noteq> n \<rbrakk> \<Longrightarrow> lvname x m t ([lstore \<leadsto> {\<guillemotleft>n\<guillemotright>} \<Zndres> lstore] s) = lvname x m t s"
  by (auto simp add: lvname_def subst_upd_def subst_id_def lens_comp_def lv_lens_def lvar_lens_def)

lemma lvname_subst_4 [simp]: "\<lbrakk> lv_lens x m \<rbrakk> \<Longrightarrow> lvname x m t ([x \<leadsto> e] s) = True"
  by (auto simp add: lvname_def subst_upd_def subst_id_def lens_comp_def lv_lens_def lvar_lens_def pfun_lens_def uval_lens_def)

lemma lvname_subst_5 [simp]: "\<lbrakk> lv_lens x m \<rbrakk> \<Longrightarrow> lvname x m t ([lstore \<leadsto> {\<guillemotleft>m\<guillemotright>} \<Zndres> lstore] s) = False"
  by (auto simp add: lvname_def subst_upd_def subst_id_def lens_comp_def lv_lens_def lvar_lens_def pfun_lens_def uval_lens_def)

lemma lvget_subst [simp]: "\<lbrakk> lv_lens x m; m \<noteq> n \<rbrakk> \<Longrightarrow> get\<^bsub>x\<^esub> ([lstore \<leadsto> {\<guillemotleft>n\<guillemotright>} \<Zndres> $lstore] s) = get\<^bsub>x\<^esub> s"
  by (auto simp add: lvname_def subst_upd_def subst_id_def lens_comp_def lv_lens_def lvar_lens_def pfun_lens_def uval_lens_def)

syntax "_lvname" :: "id \<Rightarrow> type \<Rightarrow> logic" ("LV'(_::_')")
translations "LV(x :: 'a)" => "CONST lvname x IDLIT(x) TYPE('a)"
translations "LV(x :: 'a)" <= "CONST lvname x y TYPE('a)"

text \<open> For convenience, we can use the notation @{term "LV(n::'a::injval)"} to mean that the lens bound to
  identifier @{term n} is defined in a given state. The syntax translation engine inserts the 
  string corresponding to the identifier (e.g. @{term "STR ''x''"})
  \<close>

subsection \<open> Variable Blocks \<close>

text \<open> Extend the variable stack \<close>

definition open_var :: "uname \<Rightarrow> utype \<Rightarrow> ('e, 'a lvar_scheme) htree" where
"open_var n a = (\<exclamdown>\<guillemotleft>n\<guillemotright> \<notin> pdom lstore! ;; lstore := lstore \<oplus> {\<guillemotleft>n\<guillemotright> \<mapsto> uval_default \<guillemotleft>a\<guillemotright>}\<^sub>p)"

text \<open> Reduce the variable stack \<close>

definition close_var :: "uname \<Rightarrow> ('e, 'a lvar_scheme) htree" where
"close_var n = (lstore := {\<guillemotleft>n\<guillemotright>} \<Zndres> lstore)"

text \<open> Create a local variable block \<close>

definition vblock :: "uname \<Rightarrow> 'v itself \<Rightarrow> (('v::injval \<Longrightarrow> 'a lvar_scheme) \<Rightarrow> ('e, 'a lvar_scheme) htree) \<Rightarrow> ('e, 'a lvar_scheme) htree"
  where "vblock n t B = open_var n (utyp TYPE('v))  ;; let_itree (SEXP (\<lambda> s. lvar_lens n)) B ;; close_var n"

syntax "_vblock" :: "id \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var _ :: _./ _" [0, 0, 10] 10)

translations 
  "_vblock x t e" => "CONST vblock IDLIT(x) (_TYPE t) (_lvar_abs x t e)"
  "_vblock x t e" <= "CONST vblock n (_TYPE t) (\<lambda> x. e)"

lemma hl_vblock [hoare_safe]:
  assumes
    "\<And> x. lv_lens x n \<Longrightarrow> H{lvname x n TYPE('t) \<and> P\<lbrakk>{\<guillemotleft>n\<guillemotright>} \<Zndres> lstore/lstore\<rbrakk>} B x {Q\<lbrakk>{\<guillemotleft>n\<guillemotright>} \<Zndres> lstore/lstore\<rbrakk>}"
  shows "H{P} vblock n TYPE('t::injval) (\<lambda> x. B x) {Q}"
  apply (simp add: vblock_def open_var_def close_var_def kcomp_assoc)
  apply (rule hoare_safe)
  apply (rule hoare_safe)
    apply simp
   apply (rule hoare_safe)
   apply (rule hoare_safe)
   apply (rule hl_conseq)
     apply (rule assms(1))
     apply (simp add: lv_lens_def)
    apply (simp add: lv_lens_def lvname_def uvals_def)
    apply expr_auto
   apply expr_simp
  apply auto[1]
  done

end