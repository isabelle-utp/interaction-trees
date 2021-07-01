theory Euclidean_Algorithm
  imports "../ITree_Extraction"
begin lit_vars

alphabet gcd = 
  a :: integer
  b :: integer

definition eucl_gcd :: "(_, gcd) htree" where
"eucl_gcd = while a \<noteq> b do if a > b then a := a - b else b := b - a fi od"

end