section \<open> Collatz Conjecture \<close>

theory Collatz_Conjecture
  imports "ITree_VCG.ITree_VCG"
begin

zstore state = 
  n :: nat
  hist :: "nat list"

program collatz "N :: nat" over state = 
  "n := N ;
   hist := [n] ;
   while n \<noteq> 1 inv True do
     if even n then n := n div 2 else n := 3*n + 1 fi ;
     hist := hist @ [n]
   od"

execute "collatz 2"
execute "collatz 3"
execute "collatz 4"
execute "collatz 5"
execute "collatz 6"
execute "collatz 7"
execute "collatz 27"

lemma "\<^bold>{True\<^bold>} collatz N \<^bold>{n = 1\<^bold>}"
  by vcg

end