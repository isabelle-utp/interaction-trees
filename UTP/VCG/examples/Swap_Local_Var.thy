theory Swap_Local_Var
  imports "ITree_VCG.ITree_VCG"
begin

zstore st = lvstore +
  x :: int
  y :: int

lemma swap_correct_1: "H{x = X \<and> y = Y} var z::int. z := x ; x := y ; y := z {x = Y \<and> y = X}" 
  apply (rule hl_vblock)
  apply (subst_eval)
  apply (rule hoare_safe, simp, subst_eval)
   apply (rule hoare_safe, simp, subst_eval)
    apply (rule hoare_safe, subst_eval)
   apply simp
  apply (subst lv_lens_defined)
   apply simp
  apply simp
  done

lemma swap_correct_2: "H{x = X \<and> y = Y} var z::int. z := x ; x := y ; y := z {x = Y \<and> y = X}"
  by vcg_lens

end