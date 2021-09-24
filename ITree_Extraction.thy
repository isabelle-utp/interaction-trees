subsection \<open> ITree Code Generation Support \<close>

theory ITree_Extraction
  imports ITree_Deadlock "HOL-Library.Code_Lazy"
begin

text \<open> Necessary to deal with SML value restriction \<close>

declare deadlock_def [code_unfold]

text \<open> Configuring the code generator; either partial functions or associative lists can be used
  in specifying choice functions. Partial injections are also supported using lists. \<close>

code_datatype pfun_of_alist pfun_of_map pfun_of_pinj pfun_entries
code_datatype pinj_of_alist

declare pinv_pinj_of_alist [code]

instantiation list :: (type) default
begin
definition "default_list = ([] :: 'a list)"
instance ..
end

instantiation set :: (type) default
begin
definition "default_set = ({} :: 'a set)"
instance ..
end

instantiation bool :: default
begin
definition "default_bool = False"
instance ..
end

instantiation int :: default
begin
definition "default_int = (0 :: int)"
instance ..
end

instantiation integer :: default
begin
definition "default_integer = (0 :: integer)"
instance ..
end

instantiation String.literal :: default
begin
definition "default_literal = STR ''''"
instance ..
end

instantiation pfun :: (type, type) default
begin
definition "default_pfun = ({}\<^sub>p :: ('a, 'b) pfun)"
instance ..
end

instantiation ffun :: (type, type) default
begin
definition "default_ffun = ({}\<^sub>f :: ('a, 'b) ffun)"
instance ..
end

instantiation pinj :: (type, type) default
begin
definition default_pinj :: "'a \<Zpinj> 'b" where "default_pinj = 0"
instance ..
end

declare UNIV_I [code_unfold]
declare bool_simps [code_unfold]

lemma Collect_List_member [code_unfold]: "Collect (List.member xs) = set xs"
  using in_set_member by fastforce

declare image_ident [code_unfold]

end