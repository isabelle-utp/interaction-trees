theory ITree_Machine
  imports ITree_Operations
  keywords "zmachine" "zoperation" :: "thy_decl_block"
    and "over" "init" "operations" "params" "guard" "update" "post" "\<in>"
begin

record ('a, 's) zop =
  ztype :: "'a set"
  zguard :: "'a \<Rightarrow> 's \<Rightarrow> bool"
  zupdate :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  zpost :: "'a \<Rightarrow> 's \<Rightarrow> bool"

definition moperation :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('e, 's) htree" where
[code_unfold]: "moperation c A P Q \<sigma> = input_in_where c (\<guillemotleft>A\<guillemotright>)\<^sub>e (\<lambda> v. ((\<lambda> s. P v s \<and> Q v (\<sigma> v s)), \<langle>\<sigma> v\<rangle>\<^sub>a))"

definition machine :: "('s::default) subst \<Rightarrow> ('e, 's) htree list \<Rightarrow> 'e process" where
[code_unfold]: "machine Init Ops = process Init (loop (foldr (\<box>) Ops Stop))"

ML_file \<open>ITree_Machine.ML\<close>

term zop.make

ML \<open>
Outer_Syntax.command @{command_keyword zmachine} "define a Z machine"
    (Z_Machine.parse_zmachine >> (Toplevel.local_theory NONE NONE o Z_Machine.zmachine_sem));

Outer_Syntax.command @{command_keyword zoperation} "define a Z operation"
    (Z_Machine.parse_operation >> (Toplevel.local_theory NONE NONE o Z_Machine.operation_sem'));
\<close>

end