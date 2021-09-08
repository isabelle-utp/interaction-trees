theory ITree_Machine
  imports ITree_Operations
  keywords "zmachine" "zoperation" :: "thy_decl_block"
    and "over" "init" "operations" "params" "guard" "update" "post" "\<in>"
begin

text \<open> An operation is constructed from a precondition, update, and postcondition, all of which
  are parameterised. \<close>

definition mk_zop :: "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's subst) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('e, 's) htree)" where
"mk_zop P \<sigma> Q = (\<lambda> v. assert (P v) \<Zcomp> \<langle>\<sigma> v\<rangle>\<^sub>a \<Zcomp> assume (Q v))"

text \<open> An operation requires that precondition holds, and that following the update the postcondition(s)
  also hold. \<close>

lemma wp_zop [wp, code_unfold]: "wp (mk_zop P \<sigma> Q v) b = [\<lambda> \<s>. P v \<s> \<and> (\<sigma> v \<dagger> [\<lambda> \<s>. Q v \<s> \<and> b \<s>]\<^sub>e) \<s>]\<^sub>e"
  by (simp add: mk_zop_def wp)

lemma wlp_zop [wp, code_unfold]: "wlp (mk_zop P \<sigma> Q v) b = [\<lambda> \<s>. P v \<s> \<longrightarrow> (\<sigma> v \<dagger> [\<lambda> \<s>. Q v \<s> \<longrightarrow> b \<s>]\<^sub>e) \<s>]\<^sub>e"
  by (simp add: mk_zop_def wp)

text \<open> An operation can have its parameters supplied by an event, using the construct below. \<close>

definition zop_event :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
[code_unfold]: "zop_event c A zop = input_in_where c 
                                    (\<guillemotleft>A\<guillemotright>)\<^sub>e 
                                    (\<lambda> v. (wp (zop v) True, zop v))"

text \<open> A machine has an initialisation and a list of operations. \<close>

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