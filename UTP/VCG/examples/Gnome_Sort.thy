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
     inv 0 \<le> pos \<and> pos \<le> length a 
       \<and> sorted (nths a {0..<pos})
       \<and> mset a = mset xs 
     do
       if (pos = 0 \<or> a ! pos \<ge> a ! (pos - 1))
       then pos := pos + 1
       else (a[pos], a[pos-1]) := (a ! (pos-1), a!pos); pos := pos - 1
       fi
     od"

execute "gnome_sort [5,3,5,4,2]"

lemma gnome_sort_correct: "H{True} gnome_sort xs {sorted a \<and> mset xs = mset a}"
  apply vcg
  apply (simp add: nths_single)
  apply (smt (verit) One_nat_def Suc_less_eq cancel_comm_monoid_add_class.diff_zero diff_Suc_1 less_Suc_eq less_or_eq_imp_le nth_take nths_atLeastLessThan_0_take nths_upt_length sorted_iff_nth_Suc zero_less_Suc)
  apply (metis atLeastLessThan_iff diff_le_self dual_order.strict_trans2 less_not_refl nths_list_update_out sorted_nths_atLeastLessThan_0)
  apply (simp add: mset_swap)
  apply (simp add: nths_all)
  done

end