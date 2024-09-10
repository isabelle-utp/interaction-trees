subsection \<open> Systems of Recursive ITrees \<close>

theory ITree_Recursion
  imports ITree_Iteration
begin

text \<open> A system of mutually (co)recursive ITrees can be specified as a partial function 
  @{typ "'n \<Zpfun> ('e, 'n + 'r) itree"}. Here, @{typ "'n"} provides names for individual ITrees,
  and @{typ "'r"} is for return values, as usual. An ITree of type @{typ "('e, 'n + 'r) itree"}
  is, intuitively, may either call another ITree named in @{typ "'n"} or else return 
  a value in @{typ "'r"}. This approach allows us to overcome the limitation that corecursive
  definitions may not be mutual.

  The following corecursive definition expands such a system of mutually tail corecursive equations:
\<close>

corec fixit :: "('n \<Zpfun> ('e, 'n + 'r) itree) \<Rightarrow> ('e, 'n + 'r) itree \<Rightarrow> ('e, 'r) itree" where
"fixit \<Gamma> t 
   = (case t of
        Sil t' \<Rightarrow> Sil (fixit \<Gamma> t') |
        Vis F \<Rightarrow> Vis (map_pfun (fixit \<Gamma>) F) | 
        Ret (Inl n) \<Rightarrow> if n \<in> dom \<Gamma> then Sil (fixit \<Gamma> (\<Gamma> n)) else diverge |
        Ret (Inr x) \<Rightarrow> Ret x)"

text \<open> If a name is encountered, and this is defined in the equation system, then this ITree is 
  called. If a name with no mapping is encountered, the result is divergence. \<close>

end