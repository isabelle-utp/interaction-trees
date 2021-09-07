theory ITree_Machine
  imports ITree_Operations
  keywords "zmachine" :: "thy_decl_block"
    and "over" "init" "operations" "params" "guard" "update" "post" "\<in>"
begin

definition moperation :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('e, 's) htree" where
[code_unfold]: "moperation c A P Q \<sigma> = input_in_where c (\<guillemotleft>A\<guillemotright>)\<^sub>e (\<lambda> v. ((\<lambda> s. P v s \<and> Q v (\<sigma> v s)), \<langle>\<sigma> v\<rangle>\<^sub>a))"

definition machine :: "('s::default) subst \<Rightarrow> ('e, 's) htree list \<Rightarrow> 'e process" where
[code_unfold]: "machine Init Ops = process Init (loop (foldr (\<box>) Ops Stop))"

ML_file \<open>ITree_Machine.ML\<close>

end