section \<open> Resource Manager \<close>

theory ResourceManager
  imports "Interaction_Trees.ITree_Simulation" "Interaction_Trees.ITree_Machine"
begin 

unbundle Circus_Syntax

lit_vars

consts RES :: "integer set"

schema ResourceManager =
  res  :: "integer set"
  free :: "integer set"
  where "free \<subseteq> res" "res \<subseteq> RES"

record_default ResourceManager

zoperation Allocate =
  over ResourceManager
  params r \<in> RES
  pre "r \<in> free"
  update "[free \<leadsto> free - {r}]"

zoperation Allocate\<^sub>1 =
  over ResourceManager
  params r \<in> RES
  pre "r \<in> free \<and> r = Min free"
  update "[free \<leadsto> free - {r}]"

zoperation Deallocate =
  over ResourceManager
  params r \<in> RES
  pre "r \<notin> free"
  update "[free \<leadsto> free \<union> {r}]"

lemma Allocate\<^sub>1_refines_Allocate: "Allocate r \<sqsubseteq> Allocate\<^sub>1 r"
  apply (simp add: Allocate_def Allocate\<^sub>1_def input_in_rel assigns_rel refined_by_def input_in_pre assigns_pre seq_pre wp mk_zop_def)
  oops

zmachine ResourceManagerProc =
  init "[res \<leadsto> RES, free \<leadsto> RES]"
  operations "Allocate" "Deallocate"

def_consts RES = "set (map integer_of_int [0..5])"

simulate ResourceManagerProc

export_code ResourceManagerProc in Haskell module_name ResourceManager (string_classes)

end