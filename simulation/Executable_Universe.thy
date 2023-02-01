section \<open> Executable Universe for Interaction Trees \<close>

theory Executable_Universe
  imports "Z_Toolkit.Z_Toolkit"
begin

text \<open> Aim: To support a flexible animator that can display information about the type of data that
  channels being offered accept. \<close>

type_synonym uname = String.literal

text \<open> The following universe contains types that have direct equivalents in Haskell. \<close>

datatype uval = 
  UnitV |
  BoolV (ofBoolV: bool) |
  IntV (ofIntV: integer)| 
  RatV (ofRatV: rat) |
  StringV (ofStringV: String.literal) | 
  EnumV (ofEnums: "uname set") (ofEnumV: "uname")  |
  PairV (ofPairV: "uval \<times> uval") |
  ListV (ofListV: "uval list")

datatype utyp =
  UnitT | BoolT | IntT | RatT | StringT | EnumT "uname set" | PairT "utyp \<times> utyp" | ListT utyp

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
"utyp_of (ListV xs) = do { as \<leftarrow> those (map utyp_of xs);
                           case as of
                             [] \<Rightarrow> None 
                           | (a # as) \<Rightarrow> if (\<forall> b \<in> set as. a = b) then Some a else None }"

definition uvals :: "utyp \<Rightarrow> uval set" where
"uvals a = {x. utyp_of x = Some a}"

text \<open> A class to declare injections between HOL types and parts of the universe. \<close>

class uvals =
  fixes to_uval :: "'a \<Rightarrow> uval" \<comment> \<open> Inject into the universe \<close>
  and from_uval :: "uval \<Rightarrow> 'a" \<comment> \<open> Project from the universe \<close>
  and utyp :: "'a itself \<Rightarrow> utyp" \<comment> \<open> Give the equivalent universe type for the HOL type \<close>
  assumes to_uval_typ [simp]: "utyp_of (to_uval x) = Some (utyp TYPE('a))"
  and to_uval_inv [simp]: "from_uval (to_uval x) = x"

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
  by (intro_classes; simp add: to_uval_unit_def utyp_unit_def)

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
  by (intro_classes; simp add: to_uval_int_def utyp_int_def)

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
  by (intro_classes; simp add: to_uval_integer_def utyp_integer_def)

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
  by (intro_classes; simp add: to_uval_prod_def from_uval_prod_def utyp_prod_def prod.case_eq_if)

end

end