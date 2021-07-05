theory Euclidean_Algorithm
  imports "../ITree_Extraction"
begin lit_vars

alphabet gcd = 
  a :: integer
  b :: integer


definition eucl :: "('e, (integer \<times> integer), integer, gcd) procedure" where
"eucl = 
  (proc (A, B). 
    (a, b) := (A, B) \<Zcomp> 
    while a \<noteq> b do 
      if a > b 
        then a := a - b 
        else b := b - a 
      fi 
    od \<Zcomp> 
    return a)"

record_default gcd

definition eucl_gcd where "eucl_gcd = procproc eucl"

lemma map_prod_pfun_of_map [code]:
  "map_prod (pfun_of_map f) (pfun_of_map g) = 
     pfun_of_map (\<lambda> x. case (f x, g x) of
                       (Some _, Some _) \<Rightarrow> None |
                       (Some y, None) \<Rightarrow> Some y |
                       (None, Some y) \<Rightarrow> Some y |
                       (None, None) \<Rightarrow> None)"
  by (auto simp add: map_prod_def pdom_def pdom_res_def restrict_map_def plus_pfun_def map_add_def 
      pfun_of_map_inject fun_eq_iff option.case_eq_if)

lemma map_prod_pfun_of_alist [code]:
  "map_prod (pfun_of_alist xs) (pfun_of_alist ys) =
    pfun_of_alist (AList.restrict (- fst ` set xs) ys @ AList.restrict (- fst ` set ys) xs)"
  by (simp add: map_prod_def pdom_res_alist plus_pfun_alist)




export_code eucl_gcd in Haskell module_name Euclidean_Algorithm (string_classes)

end