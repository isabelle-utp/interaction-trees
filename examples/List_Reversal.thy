theory List_Reversal
  imports "ITree_UTP.ITree_UTP"
begin lit_vars

def_consts MAX_SIL_STEPS = 100

zstore state =
  ys :: "int list"
  i :: nat

procedure reverse "xs :: int list" over state =
"ys := [] \<Zcomp> i := 0 \<Zcomp> while i < length xs inv ys = rev (take i xs) do ys := xs!i # ys \<Zcomp> i := i + 1 od"

execute "reverse [1,2,3,4]"

lemma reverse_correct: "H{True} reverse xs {ys = rev xs}"
  unfolding reverse_def
  by (hoare_auto, simp add: take_Suc_conv_app_nth)

end