section \<open> Gnome Sort \<close>

theory Gnome_Sort
  imports "ITree_VCG.ITree_VCG" "HOL-Library.Multiset"
begin

zstore gnome_st =
  a :: "int list"
  pos :: nat

program gnome_sort "xs :: int list" over gnome_st
  = "a := xs; pos := 0; 
     while pos < length a
     inv sorted (take pos a) \<and> mset a = mset xs 
     do
       if (pos = 0 \<or> a ! pos \<ge> a ! (pos - 1))
       then pos := pos + 1
       else (a[pos], a[pos-1]) := (a ! (pos-1), a ! pos); 
            pos := pos - 1
       fi
     od"

execute "gnome_sort [5,3,5,4,2]"

lemma gnome_sort_correct: "H{True} gnome_sort xs {sorted a \<and> mset xs = mset a}"
  apply vcg
  using length_greater_0_conv take_Suc_conv_app_nth apply fastforce
  apply (smt (verit) One_nat_def Suc_less_eq cancel_comm_monoid_add_class.diff_zero diff_Suc_1 less_Suc_eq less_or_eq_imp_le nth_take nths_atLeastLessThan_0_take nths_upt_length sorted_iff_nth_Suc zero_less_Suc)
  apply (metis One_nat_def Suc_diff_1 less_imp_diff_less sorted_append_middle take_hd_drop)
  apply (simp add: mset_swap)
  done

end