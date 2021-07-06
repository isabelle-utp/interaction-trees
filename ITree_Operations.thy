theory ITree_Operations
  imports ITree_Designs
begin

definition operation :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 's) htree) \<Rightarrow> ('e, 's) htree" where
"operation c P = c?(v) | pre (P v) \<rightarrow> P v"

definition io_operation :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 'b \<times> 's) htree) \<Rightarrow> ('e, 's) htree" where
"io_operation c d P = undefined"

end