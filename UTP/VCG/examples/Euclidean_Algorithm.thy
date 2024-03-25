section \<open> Euclidean Algorithm \<close>

theory Euclidean_Algorithm
  imports "ITree_VCG.ITree_VCG"
begin

zstore gcd_st = 
  a :: nat
  b :: nat

program eucl "(A::nat, B::nat)" over gcd_st =
"a := A; b := B;
 while a \<noteq> b 
   invariant a > 0 \<and> b > 0 \<and> gcd a b = gcd A B
   variant a + b
 do
   if a > b 
     then a := a - b 
     else b := b - a 
   fi 
 od"

execute "eucl (2, 8)"
execute "eucl (12, 30)"

lemma eucl_correct: "H[A > 0 \<and> B > 0] eucl (A, B) [a = gcd A B]"
  unfolding prog_defs
  apply vcg
   apply (metis gcd_diff1_nat linorder_not_less not_less_iff_gr_or_eq)
   apply (metis gcd.commute gcd_diff1_nat linorder_not_less)
  done

end