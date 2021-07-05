theory ResourceManager
  imports "../ITree_Extraction"
begin lit_vars

schema ResourceManager =
  res  :: "integer set"
  free :: "integer set"
  where "free \<subseteq> res"

record_default ResourceManager

chantype chan =
  alloc :: integer
  dealloc :: integer

definition Allocate :: "(chan, ResourceManager) htree" where
"Allocate = alloc?(r):free \<rightarrow> free := free - {r}"

text \<open> If we just select the minimum of free, the simulation crashes when all resources are allocated. 
  Adding the intersection with @{const free} means that @{term "(Min free)\<^sub>e"} is not evaluated due
  to lazy evaluation in Haskell. \<close>

definition Allocate\<^sub>1 :: "(chan, ResourceManager) htree" where
"Allocate\<^sub>1 = alloc?(r):(free \<inter> {Min free}) \<rightarrow> free := free - {r}"

lemma Allocate\<^sub>1_refines_Allocate: "Allocate \<sqsubseteq> Allocate\<^sub>1"
  by (simp add: Allocate_def Allocate\<^sub>1_def input_in_rel assigns_rel refined_by_def input_in_pre assigns_pre)
     (expr_auto)

definition Deallocate :: "(chan, ResourceManager) htree" where
"Deallocate = dealloc?(r):(res - free) \<rightarrow> free := free \<union> {r}"

definition "ResourceManagerProc R
  = process [res \<leadsto> R, free \<leadsto> R] (loop (Allocate\<^sub>1 \<box> Deallocate))"

export_code ResourceManagerProc in Haskell module_name ResourceManager (string_classes)

end