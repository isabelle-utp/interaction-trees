section \<open> ITree VCG meta-theory \<close>

theory ITree_VCG
  imports "ITree_UTP.ITree_UTP"
begin

syntax "_kleisli_comp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr ";" 54)

lit_vars

def_consts MAX_SIL_STEPS = 500

end