theory ITree_CSP_Examples
  imports "../ITree_CSP"
begin

corec speak :: "('e, 's) itree" where
"speak = Vis (map_pfun (\<lambda> _. Sil speak) pId)"

lemma "div_free speak"
  (* We need to find the right pattern to find divergence freedom using Tarki theorem *)
  apply (coinduct rule: div_free_coind[where \<phi>="\<lambda> x. \<exists> n. x = Sils n speak"])
  (* We need to show two things: (1) the our target process fits the pattern, and
  (2) that it is a prefixed-point. *)
  apply (rule_tac x="0" in exI)
  apply (simp)
  apply (auto)
  apply (induct_tac n)
  apply (simp)
  apply (subst speak.code) back
   apply (rule vis_stbs)
   apply (simp add: pfun.set_map)
  apply (rule_tac x="1" in exI, simp)
  apply (simp)
  apply (rule sil_stbs)
  apply (simp)
  done

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
  apply (rule trace_to_Sil)
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