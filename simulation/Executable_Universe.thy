section \<open> Executable Universe for Interaction Trees \<close>

theory Executable_Universe
  imports Code_Target_Rational "Z_Toolkit.Z_Toolkit" 
begin

text \<open> Aim: To support a flexible animator that can display information about the type of data that
  channels being offered accept. \<close>

type_synonym uname = String.literal

text \<open> The following universe contains types that have direct equivalents in Haskell. \<close>

datatype utyp =
  UnitT | BoolT | IntT | RatT | StringT | EnumT "uname set" | PairT "utyp \<times> utyp" | ListT utyp

datatype uval = 
  UnitV |
  BoolV (ofBoolV: bool) |
  IntV (ofIntV: integer)| 
  RatV (ofRatV: rational) |
  StringV (ofStringV: String.literal) | 
  EnumV (ofEnums: "uname set") (ofEnumV: "uname")  |
  PairV (ofPairV: "uval \<times> uval") |
  ListV utyp (ofListV: "uval list")

instantiation utyp :: "show"
begin

fun show_utyp :: "utyp \<Rightarrow> String.literal" where
  "show_utyp IntT = STR ''integer''"

instance ..

end

text \<open> Infer the type of a valid @{typ uval}. It's best to stick to a monomorphic type system,
  to make animation easier (i.e. each value maps to one type). \<close>

fun utyp_of :: "uval \<Rightarrow> utyp option" where
"utyp_of UnitV = Some UnitT" |
"utyp_of (BoolV _) = Some BoolT" |
"utyp_of (IntV _) = Some IntT" |
"utyp_of (RatV _) = Some RatT" |
"utyp_of (StringV _) = Some StringT" |
"utyp_of (EnumV A _) = Some (EnumT A)" |
"utyp_of (PairV p) = do { a \<leftarrow> utyp_of (fst p); b \<leftarrow> utyp_of (snd p); Some (PairT (a, b)) }" |
"utyp_of (ListV a xs) = do { as \<leftarrow> those (map utyp_of xs);
                             if (as = [] \<or> (\<forall> a'\<in> set as. a' = a)) then Some (ListT a) else None }"

abbreviation utyp_rel :: "uval \<Rightarrow> utyp \<Rightarrow> bool" (infix ":\<^sub>u" 50) where
"x :\<^sub>u t \<equiv> utyp_of x = Some t"

lemma utyp_UnitT_is_UnitV [elim]: "\<lbrakk> x :\<^sub>u UnitT; x = UnitV \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induct x, auto)

lemma utyp_BoolT_is_BoolV [elim]: "\<lbrakk> x :\<^sub>u BoolT; \<And> n. x = BoolV n \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induct x, auto)

lemma utyp_IntT_is_IntV [elim]: "\<lbrakk> x :\<^sub>u IntT; \<And> n. x = IntV n \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induct x, auto)

lemma utyp_RatT_is_RatV [elim]: "\<lbrakk> x :\<^sub>u RatT; \<And> n. x = RatV n \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induct x, auto)

lemma utyp_StringT_is_StringV [elim]: "\<lbrakk> x :\<^sub>u StringT; \<And> n. x = StringV n \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induct x, auto)

lemma utyp_EnumT_is_EnumV [elim]: "\<lbrakk> x :\<^sub>u EnumT A; \<And> n. x = EnumV A n \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induct x, auto)

lemma utyp_PairT_is_PairV [elim]: "\<lbrakk> x :\<^sub>u PairT (a, b); \<And> y z. \<lbrakk> x = PairV (y, z); y :\<^sub>u a; z :\<^sub>u b \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induct x, auto)

lemma utyp_ListT_ListV_ex: "x :\<^sub>u ListT a \<Longrightarrow> \<exists> xs. x = ListV a xs \<and> (\<forall> y\<in>set xs. y :\<^sub>u a)"
  apply (induct x, auto)
  sorry

lemma utyp_ListT_is_ListV [elim]: "\<lbrakk> x :\<^sub>u ListT a; \<And> xs. \<lbrakk> x = ListV a xs; (\<forall> y\<in>set xs. y :\<^sub>u a) \<rbrakk>  \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using utyp_ListT_ListV_ex by blast
  
definition uvals :: "utyp \<Rightarrow> uval set" where
"uvals a = {x. utyp_of x = Some a}"

fun default_uval :: "utyp \<Rightarrow> uval" where
"default_uval UnitT = UnitV" |
"default_uval BoolT = (BoolV False)" |
"default_uval IntT = (IntV 0)" |
"default_uval RatT = (RatV 0)" |
"default_uval StringT = (StringV STR '''')" |
"default_uval (EnumT A) = (EnumV A STR '''')" |
"default_uval (PairT (a, b)) = (PairV (default_uval a, default_uval b))" |
"default_uval (ListT a) = (ListV a [])"

lemma utyp_of_default_uval: "utyp_of (default_uval t) = Some t"
  by (induct t rule:default_uval.induct, simp_all)

text \<open> A class to declare injections between HOL types and parts of the universe. \<close>

class uvals =
  fixes to_uval :: "'a \<Rightarrow> uval" \<comment> \<open> Inject into the universe \<close>
  and from_uval :: "uval \<Rightarrow> 'a" \<comment> \<open> Project from the universe \<close>
  and utyp :: "'a itself \<Rightarrow> utyp" \<comment> \<open> Give the equivalent universe type for the HOL type \<close>
  assumes to_uval_typ [simp]: "to_uval x :\<^sub>u utyp TYPE('a)"
  and to_uval_inv [simp]: "from_uval (to_uval x) = x"
  and from_uval_inv: "\<lbrakk> v :\<^sub>u utyp TYPE('a) \<rbrakk> \<Longrightarrow> to_uval (from_uval v) = v"

lemma utyp_of_comp_to_uval: "(utyp_of \<circ> (to_uval :: 'a \<Rightarrow> uval)) = (\<lambda> _. Some (utyp TYPE('a::uvals)))"
  by (simp add: comp_def fun_eq_iff)

lemma from_after_to_uval [simp]: "from_uval \<circ> to_uval = id"
  by (simp add: comp_def fun_eq_iff)

syntax "_utyp" :: "type \<Rightarrow> logic" ("UTYPE'(_')")
translations "UTYPE('a)" == "CONST utyp TYPE('a)"

instantiation unit :: uvals
begin

definition to_uval_unit :: "unit \<Rightarrow> uval" where
  "to_uval_unit x = UnitV"

fun from_uval_unit :: "uval \<Rightarrow> unit" where
  "from_uval_unit x = ()"

definition utyp_unit :: "unit itself \<Rightarrow> utyp" where
  "utyp_unit a = UnitT"

instance
  by (intro_classes; auto simp add: to_uval_unit_def utyp_unit_def)

end

instantiation int :: uvals
begin

definition to_uval_int :: "int \<Rightarrow> uval" where
  "to_uval_int x = IntV (integer_of_int x)"

fun from_uval_int :: "uval \<Rightarrow> int" where
  "from_uval_int (IntV x) = int_of_integer x" | "from_uval_int _ = 0"

definition utyp_int :: "int itself \<Rightarrow> utyp" where
  "utyp_int a = IntT"

instance
  by (intro_classes; auto simp add: to_uval_int_def utyp_int_def)

end

instantiation integer :: uvals
begin

definition to_uval_integer :: "integer \<Rightarrow> uval" where
  "to_uval_integer x = IntV x"

fun from_uval_integer :: "uval \<Rightarrow> integer" where
  "from_uval_integer (IntV x) = x" | "from_uval_integer _ = 0"

definition utyp_integer :: "integer itself \<Rightarrow> utyp" where
  "utyp_integer a = IntT"

instance
  by (intro_classes; auto simp add: to_uval_integer_def utyp_integer_def)

end

instantiation prod :: (uvals, uvals) uvals
begin

definition to_uval_prod :: "'a \<times> 'b \<Rightarrow> uval" where
  "to_uval_prod = (\<lambda> (x, y). PairV (to_uval x, to_uval y))"

definition from_uval_prod :: "uval \<Rightarrow> 'a \<times> 'b" where
  "from_uval_prod p = map_prod from_uval from_uval (ofPairV p)"

definition utyp_prod :: "('a \<times> 'b) itself \<Rightarrow> utyp" where
  "utyp_prod a = PairT (UTYPE('a), UTYPE('b))"

instance
  by (intro_classes; auto simp add: to_uval_prod_def from_uval_prod_def utyp_prod_def prod.case_eq_if from_uval_inv)

end

lemma those_replicate_Some [simp]: "those (replicate n (Some v)) = Some (replicate n v)"
  by (induct n, simp_all)

instantiation list :: (uvals) uvals
begin

definition to_uval_list :: "'a list \<Rightarrow> uval" where
  "to_uval_list = (\<lambda> xs. ListV UTYPE('a) (map to_uval xs))"

definition from_uval_list :: "uval \<Rightarrow> 'a list" where
  "from_uval_list xs = map from_uval (ofListV xs)"

definition utyp_list :: "'a list itself \<Rightarrow> utyp" where
  "utyp_list a = ListT UTYPE('a)"

instance
  by (intro_classes, auto simp add: to_uval_list_def from_uval_list_def utyp_list_def utyp_of_comp_to_uval map_replicate_const from_uval_inv map_idI)

end

end