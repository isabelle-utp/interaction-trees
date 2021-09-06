theory ITree_Machine
  imports ITree_Operations
begin

definition moperation :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('e, 's) htree" where
[code_unfold]: "moperation c A P Q \<sigma> = input_in_where c A (\<lambda> v. ((\<lambda> s. P v s \<and> Q v (\<sigma> s)), \<langle>\<sigma>\<rangle>\<^sub>a))"

definition machine :: "('s::default) subst \<Rightarrow> ('e, 's) htree list \<Rightarrow> 'e process" where
[code_unfold]: "machine Init Ops = process Init (loop (foldr (\<box>) Ops Stop))"

end