theory ITree_CSP_Examples
  imports "../ITree_CSP"
begin

corec speak :: "('e, 's) itree" where
"speak = Vis (map_pfun (\<lambda> _. Sil speak) pId)"

lemma div_free_speak: "div_free speak"
proof -
  text \<open> The pattern for divergence freedom \<close>
  have d: "\<And> n. div_free (Sils n speak)"
    apply (coinduction rule: div_free_coinduct)
     apply (metis Sils_diverge Sils_injective diverge_not_Vis speak.code)
    apply (metis (no_types, lifting) Sils.simps(2) Sils_Vis_inj Vis_Sils map_pfun_apply pdom_map_pfun speak.code)
    done
  from d[of 0] show ?thesis by simp
qed 

chantype Chan =
  Input :: integer
  Output :: integer
  State :: "integer list"

definition "echo = loop (\<lambda>_. do { i \<leftarrow> inp Input; outp Output i })"

lemma "echo () \<midarrow>[build\<^bsub>Input\<^esub> 1, build\<^bsub>Output\<^esub> 1]\<leadsto> echo ()"
  apply (subst echo_def)
  apply (subst while.code)
  apply (subst echo_def[THEN sym])
  apply (simp)
  apply (simp add: inp_in_def)
  apply (subst bind_itree.code)
  oops

definition "buffer = 
  loop (\<lambda> s. 
      do { i \<leftarrow> inp_in Input {0,1,2,3}; Ret (s @ [i]) }
    \<box> do { guard (length s > 0); outp Output (hd s); Ret (tl s) }
    \<box> do { outp State s; Ret s }
  )"

export_code echo buffer in Haskell module_name CSP_Examples file_prefix CSP_Examples (string_classes) 

end