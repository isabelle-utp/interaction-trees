theory Euclidean_Algorithm
  imports "ITree_VCG.ITree_VCG"
begin lit_vars

zstore gcd_st = 
  a :: int
  b :: int

procedure eucl "(A::int, B::int)" over gcd_st =
"(a, b) := (A, B) ;
 while a \<noteq> b inv a > 0 \<and> b > 0 \<and> gcd a b = gcd A B do 
   if a > b 
     then a := a - b 
     else b := b - a 
   fi 
 od"

execute "eucl (2, 8)"
execute "eucl (12, 30)"

lemma eucl_correct: "\<^bold>{A > 0 \<and> B > 0\<^bold>} eucl (A, B) \<^bold>{a = gcd A B\<^bold>}"
  unfolding eucl_def
  apply (hoare_auto)
  apply (simp add: gcd_diff1 gcd_integer.rep_eq integer_eq_iff)
  apply (metis gcd.commute gcd_diff1)
  done

end