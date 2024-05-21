theory Show_Channel
  imports "Interaction_Trees.ITrees"
begin

definition show_channel :: "String.literal \<Rightarrow> 'a::show \<Rightarrow> String.literal" where
"show_channel c p = c + STR '' '' + show p"

ML_file \<open>Show_Channel.ML\<close>

end