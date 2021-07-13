theory Euclidean_Algorithm
  imports "../ITree_Extraction"
begin lit_vars

alphabet gcd = 
  a :: integer
  b :: integer

record_default gcd

definition eucl :: "integer \<times> integer \<Rightarrow> ('e, gcd) htree" where
  "eucl \<equiv>
   (\<lambda> (A, B). 
    (a, b) := (A, B) \<Zcomp> 
    while a \<noteq> b inv a > 0 \<and> b > 0 \<and> gcd a b = gcd A B do 
      if a > b 
        then a := a - b 
        else b := b - a 
      fi 
    od)"

definition eucl_proc :: "('e, (integer \<times> integer), integer, gcd) procedure" where
"eucl_proc = (proc (A, B). eucl(A, B) \<Zcomp> return a)"

lemma eucl_correct: "\<^bold>{A > 0 \<and> B > 0\<^bold>} eucl (A, B) \<^bold>{a = gcd A B\<^bold>}"
  unfolding eucl_def
  apply (simp)
  apply (rule hoare_fwd_assign)
   apply (simp)
  apply (simp add: usubst_eval SEXP_apply)
  apply (rule hoare_while_inv_partial)
    apply (rule hoare_safe)
     apply (rule hoare_safe)
     apply (simp add: usubst_eval, expr_auto)
     apply (simp add: gcd_diff1 gcd_integer.rep_eq integer_eq_iff)
    apply (rule hoare_safe)
    apply (simp add: usubst_eval, expr_auto)
    apply (smt (verit, ccfv_SIG) gcd_add2 gcd_integer.rep_eq integer_eq_iff minus_integer.rep_eq)
   apply (expr_auto)
  apply (expr_auto)
  apply (smt (verit) gcd.commute gcd_code_int gcd_diff1 gcd_integer.rep_eq integer_eq_iff less_integer.rep_eq zero_integer.rep_eq)
  done

definition eucl_gcd where "eucl_gcd = procproc eucl_proc"

export_code eucl_gcd in Haskell module_name Euclidean_Algorithm (string_classes)

end