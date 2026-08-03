section \<open> Local Variable Blocks \<close>

theory ITree_Local_Var
  imports ITree_Hoare
begin

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

class lvar =
  fixes lstore :: "(uname \<Zpfun> uval) \<Longrightarrow> 'a"
  assumes lstore_vwb [simp]: "vwb_lens lstore"

zstore lvstore =
  local_store :: "uname \<Zpfun> uval"

instantiation lvstore_ext :: (type) lvar
begin

definition lstore_lvstore_ext :: "uname \<Zpfun> uval \<Longrightarrow> 'a lvstore_scheme"
  where "lstore_lvstore_ext = local_store"

instance by (intro_classes, simp add: lstore_lvstore_ext_def)

end

lemma local_store_indeps [simp]: 
  "x \<bowtie> local_store \<Longrightarrow> x \<bowtie> lstore"
  "local_store \<bowtie> x \<Longrightarrow> lstore \<bowtie> x"
  by (simp_all add: lstore_lvstore_ext_def)

text \<open> The following instance allows the use of return values as the first component of a pair. The
  store is therefore in the state, which is the second component. \<close>

instantiation prod :: (type, lvar) lvar
begin

definition lstore_prod :: "uname \<Zpfun> uval \<Longrightarrow> 'a \<times> 'b" where
"lstore_prod = (lstore ;\<^sub>L snd\<^sub>L)"

instance
  by (intro_classes, simp add: lstore_prod_def comp_vwb_lens)

end

subsection \<open> Local Variable Lenses \<close>

text \<open> The local variable lens projects the store, followed by the value (@{typ uval}) at the given 
  name, followed by projecting out a value of the correct type. \<close>

definition lvar_lens :: "uname \<Rightarrow> ('a::injval \<Longrightarrow> 's::lvar)" where 
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

definition lv_lens :: "('a::injval \<Longrightarrow> 's::lvar) \<Rightarrow> uname \<Rightarrow> bool" where
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

definition lvname :: "('a::injval \<Longrightarrow> 's::lvar) \<Rightarrow> uname \<Rightarrow> 'a itself \<Rightarrow> 's::lvar \<Rightarrow> bool" where 
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

definition open_var :: "uname \<Rightarrow> utype \<Rightarrow> ('e, 's::lvar) htree" where
"open_var n a = (\<exclamdown>\<guillemotleft>n\<guillemotright> \<notin> pdom lstore! ;; lstore := lstore \<oplus> {\<guillemotleft>n\<guillemotright> \<mapsto> uval_default \<guillemotleft>a\<guillemotright>}\<^sub>p)"

text \<open> Reduce the variable stack \<close>

definition close_var :: "uname \<Rightarrow> ('e, 's::lvar) htree" where
"close_var n = (lstore := {\<guillemotleft>n\<guillemotright>} \<Zndres> lstore)"

text \<open> Create a local variable block \<close>

definition vblock :: "uname \<Rightarrow> 'v itself \<Rightarrow> (('v::injval \<Longrightarrow> 's::lvar) \<Rightarrow> 's \<Rightarrow> ('e, 't::lvar) itree) \<Rightarrow> 's \<Rightarrow> ('e, 't) itree"
  where "vblock n t B = open_var n (utyp TYPE('v))  ;; let_itree (SEXP (\<lambda> s. lvar_lens n)) B ;; close_var n"

adhoc_overloading uvarblock \<rightleftharpoons> vblock

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