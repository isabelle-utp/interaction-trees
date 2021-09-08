theory ITree_Machine
  imports ITree_Operations
  keywords "zmachine" "zoperation" :: "thy_decl_block"
    and "over" "init" "operations" "params" "guard" "update" "post" "\<in>"
begin

record ('a, 's) zop =
  ztype :: "'a set"
  zpre :: "'a \<Rightarrow> 's \<Rightarrow> bool"
  zupdate :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  zpost :: "'a \<Rightarrow> 's \<Rightarrow> bool"

lemma zop_unfolds [simp, code_unfold]: 
  "ztype (zop.make t p \<sigma> q) = t"
  "zpre (zop.make t p \<sigma> q) = p"
  "zupdate (zop.make t p \<sigma> q) = \<sigma>"
  "zpost (zop.make t p \<sigma> q) = q"
  by (simp_all add: zop.defs)

definition zop_sem :: "('a, 's) zop \<Rightarrow> ('a \<Rightarrow> ('e, 's) htree)" where
[code_unfold]: "zop_sem zop = (\<lambda> v. assert (zpre zop v) \<Zcomp> \<langle>zupdate zop v\<rangle>\<^sub>a \<Zcomp> assert (zpost zop v))"

definition zop_event :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a, 's) zop \<Rightarrow> ('e, 's) htree" where
[code_unfold]: "zop_event c zop = input_in_where c 
                                  (\<guillemotleft>ztype zop\<guillemotright>)\<^sub>e 
                                  (\<lambda> v. ((\<lambda> s. zpre zop v s \<and> zpost zop v (zupdate zop v s)), zop_sem zop v))"

lemma
  "zop_event c zop = input_in_where c 
                                  (\<guillemotleft>ztype zop\<guillemotright>)\<^sub>e 
                                  (\<lambda> v. ((\<lambda> s. zpre zop v s \<and> zpost zop v (zupdate zop v s)), \<langle>zupdate zop v\<rangle>\<^sub>a))"
  oops

definition machine :: "('s::default) subst \<Rightarrow> ('e, 's) htree list \<Rightarrow> 'e process" where
[code_unfold]: "machine Init Ops = process Init (loop (foldr (\<box>) Ops Stop))"

ML_file \<open>ITree_Machine.ML\<close>

ML \<open>
Outer_Syntax.command @{command_keyword zmachine} "define a Z machine"
    (Z_Machine.parse_zmachine >> (Toplevel.local_theory NONE NONE o Z_Machine.zmachine_sem));

Outer_Syntax.command @{command_keyword zoperation} "define a Z operation"
    (Z_Machine.parse_operation >> (Toplevel.local_theory NONE NONE o Z_Machine.mk_zop));
\<close>


end