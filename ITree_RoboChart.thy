section \<open> RoboChart semantics \<close>

theory ITree_RoboChart
  imports "ITree_CSP" "Enum_Type"
begin

subsection \<open> CSP operators \<close>
definition par_hide where
"par_hide P s Q = (hide (P \<parallel>\<^bsub> s \<^esub> Q) s)"

definition prhide where
"prhide P es = foldl (\<lambda> Q e. hide Q {e}) P es"

definition discard_state where
"discard_state P = do {P ; skip}"

subsection \<open> RoboChart types \<close>
type_synonym core_int = integer

fun int2integer_list :: "int list \<Rightarrow> integer list" where
"int2integer_list Nil = Nil" |
"int2integer_list (Cons x xs) 
  = Cons (integer_of_int x) (int2integer_list xs)"

definition int_to_integer_list :: "int list \<Rightarrow> integer list" where
"int_to_integer_list = map (integer_of_int)"

lemma "int2integer_list xs = int_to_integer_list xs"
  apply (simp add: int_to_integer_list_def)
  apply (induction xs)
  apply simp
  by simp

subsection \<open> RoboChart CSP datatypes \<close>

datatype InOut = din | dout

definition "InOut_list = [din, dout]"
definition "InOut_set = set InOut_list"

enumtype Din = c1 | c2

ML \<open> 
($$ "h") (Symbol.explode "hello");
val hw = Scan.one (fn x => x = "h" orelse x = "o");
hw (Symbol.explode "hello");
hw (Symbol.explode "ollo");
\<close>

end