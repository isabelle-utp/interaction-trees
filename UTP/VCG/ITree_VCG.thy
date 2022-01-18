section \<open> ITree VCG meta-theory \<close>

theory ITree_VCG
  imports "Explorer.Explorer" "ITree_UTP.ITree_UTP"
begin

syntax "_kleisli_comp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr ";" 54)

lit_vars

setup Explorer_Lib.switch_to_quotes

def_consts MAX_SIL_STEPS = 500

lemma nth'_as_nth [simp]: "k < length xs \<Longrightarrow> nth' xs k = nth xs k"
  by (simp add: nth'_def)

declare list_augment_as_update [simp] 

declare nth_list_update [simp]

end