theory List_Reversal
  imports "ITree_UTP.ITree_UTP"
begin 

term "[\<lambda> s. R i s]\<^sub>e"
term "[\<lambda> s. R s i]\<^sub>e"

lit_vars

syntax
  "_kleisli_comp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr ";" 54)

def_consts MAX_SIL_STEPS = 100

zstore state =
  ys :: "int list"
  i :: nat

procedure reverse "xs :: int list" over state =
"ys := [] ; i := 0 ; 
 while i < length xs inv ys = rev (take i xs) 
 do 
    ys := xs!i # ys; 
    i := i + 1 
 od"

procedure reverse' "xs :: int list" over state =
"ys := [];
 for x in xs inv j. ys = rev (take j xs) do ys := x # ys od"

execute "reverse [1,2,3,4]"
execute "reverse' [1,2,3,4]"

lemma reverse_correct: "H{True} reverse xs {ys = rev xs}"
  unfolding reverse_def
  by (hoare_auto, simp add: take_Suc_conv_app_nth)

lemma reverse_correct': "H{True} reverse' xs {ys = rev xs}"
  unfolding reverse'_def
  by (hoare_auto, simp add: take_Suc_conv_app_nth)

end